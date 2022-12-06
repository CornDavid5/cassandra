/*
 * Licensed to the Apache Software Foundation (ASF) under one
 * or more contributor license agreements.  See the NOTICE file
 * distributed with this work for additional information
 * regarding copyright ownership.  The ASF licenses this file
 * to you under the Apache License, Version 2.0 (the
 * "License"); you may not use this file except in compliance
 * with the License.  You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package org.apache.cassandra.config;

import java.io.File;
import java.io.IOException;
import java.net.*;
import java.nio.file.FileStore;
import java.nio.file.NoSuchFileException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.*;
import java.util.concurrent.TimeUnit;
import java.util.function.Function;
import java.util.function.Supplier;

import com.google.common.annotations.VisibleForTesting;
import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableSet;
import com.google.common.primitives.Ints;
import com.google.common.primitives.Longs;
import com.google.common.util.concurrent.RateLimiter;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import org.apache.cassandra.audit.AuditLogOptions;
import org.apache.cassandra.fql.FullQueryLoggerOptions;
import org.apache.cassandra.auth.AllowAllInternodeAuthenticator;
import org.apache.cassandra.auth.AuthConfig;
import org.apache.cassandra.auth.IAuthenticator;
import org.apache.cassandra.auth.IAuthorizer;
import org.apache.cassandra.auth.IInternodeAuthenticator;
import org.apache.cassandra.auth.INetworkAuthorizer;
import org.apache.cassandra.auth.IRoleManager;
import org.apache.cassandra.config.Config.CommitLogSync;
import org.apache.cassandra.db.ConsistencyLevel;
import org.apache.cassandra.db.commitlog.AbstractCommitLogSegmentManager;
import org.apache.cassandra.db.commitlog.CommitLog;
import org.apache.cassandra.db.commitlog.CommitLogSegmentManagerCDC;
import org.apache.cassandra.db.commitlog.CommitLogSegmentManagerStandard;
import org.apache.cassandra.dht.IPartitioner;
import org.apache.cassandra.exceptions.ConfigurationException;
import org.apache.cassandra.io.FSWriteError;
import org.apache.cassandra.io.util.DiskOptimizationStrategy;
import org.apache.cassandra.io.util.FileUtils;
import org.apache.cassandra.io.util.SpinningDiskOptimizationStrategy;
import org.apache.cassandra.io.util.SsdDiskOptimizationStrategy;
import org.apache.cassandra.locator.DynamicEndpointSnitch;
import org.apache.cassandra.locator.EndpointSnitchInfo;
import org.apache.cassandra.locator.IEndpointSnitch;
import org.apache.cassandra.locator.InetAddressAndPort;
import org.apache.cassandra.locator.Replica;
import org.apache.cassandra.locator.SeedProvider;
import org.apache.cassandra.security.EncryptionContext;
import org.apache.cassandra.security.SSLFactory;
import org.apache.cassandra.service.CacheService.CacheType;
import org.apache.cassandra.utils.FBUtilities;

import org.apache.commons.lang3.ArrayUtils;
import org.apache.commons.lang3.StringUtils;

import static java.util.concurrent.TimeUnit.MILLISECONDS;
import static org.apache.cassandra.config.CassandraRelevantProperties.OS_ARCH;
import static org.apache.cassandra.config.CassandraRelevantProperties.SUN_ARCH_DATA_MODEL;
import static org.apache.cassandra.io.util.FileUtils.ONE_GB;
import static org.apache.cassandra.io.util.FileUtils.ONE_MB;

public class DatabaseDescriptor
{
    static
    {
        // This static block covers most usages
        FBUtilities.preventIllegalAccessWarnings();
        System.setProperty("io.netty.transport.estimateSizeOnSubmit", "false");
    }

    private static final Logger logger = LoggerFactory.getLogger(DatabaseDescriptor.class);

    /**
     * Tokens are serialized in a Gossip VersionedValue String.  VV are restricted to 64KB
     * when we send them over the wire, which works out to about 1700 tokens.
     */
    private static final int MAX_NUM_TOKENS = 1536;

    private static Config conf;

    /**
     * Request timeouts can not be less than below defined value (see CASSANDRA-9375)
     */
    static final long LOWEST_ACCEPTED_TIMEOUT = 10L;

    private static IEndpointSnitch snitch;
    private static InetAddress listenAddress; // leave null so we can fall through to getLocalHost
    private static InetAddress broadcastAddress;
    private static InetAddress rpcAddress;
    private static InetAddress broadcastRpcAddress;
    private static SeedProvider seedProvider;
    private static IInternodeAuthenticator internodeAuthenticator = new AllowAllInternodeAuthenticator();

    /* Hashing strategy Random or OPHF */
    private static IPartitioner partitioner;
    private static String paritionerName;

    private static Config.DiskAccessMode indexAccessMode;

    private static IAuthenticator authenticator;
    private static IAuthorizer authorizer;
    private static INetworkAuthorizer networkAuthorizer;
    // Don't initialize the role manager until applying config. The options supported by CassandraRoleManager
    // depend on the configured IAuthenticator, so defer creating it until that's been set.
    private static IRoleManager roleManager;

    private static long preparedStatementsCacheSizeInMB;

    private static long keyCacheSizeInMB;
    private static long counterCacheSizeInMB;
    private static long indexSummaryCapacityInMB;

    private static String localDC;
    private static Comparator<Replica> localComparator;
    private static EncryptionContext encryptionContext;
    private static boolean hasLoggedConfig;

    private static DiskOptimizationStrategy diskOptimizationStrategy;

    private static boolean clientInitialized;
    private static boolean toolInitialized;
    private static boolean daemonInitialized;

    private static final int searchConcurrencyFactor = Integer.parseInt(System.getProperty(Config.PROPERTY_PREFIX + "search_concurrency_factor", "1"));

    private static volatile boolean disableSTCSInL0 = Boolean.getBoolean(Config.PROPERTY_PREFIX + "disable_stcs_in_l0");
    private static final boolean unsafeSystem = Boolean.getBoolean(Config.PROPERTY_PREFIX + "unsafesystem");

    // turns some warnings into exceptions for testing
    private static final boolean strictRuntimeChecks = Boolean.getBoolean("cassandra.strict.runtime.checks");

    public static volatile boolean allowUnlimitedConcurrentValidations = Boolean.getBoolean("cassandra.allow_unlimited_concurrent_validations");

    private static Function<CommitLog, AbstractCommitLogSegmentManager> commitLogSegmentMgrProvider = c -> DatabaseDescriptor.isCDCEnabled()
                                       ? new CommitLogSegmentManagerCDC(c, DatabaseDescriptor.getCommitLogLocation())
                                       : new CommitLogSegmentManagerStandard(c, DatabaseDescriptor.getCommitLogLocation());

    public static void daemonInitialization() throws ConfigurationException
    {
        daemonInitialization(DatabaseDescriptor::loadConfig);
    }

    public static void daemonInitialization(Supplier<Config> config) throws ConfigurationException
    {
        if (toolInitialized)
            throw new AssertionError("toolInitialization() already called");
        if (clientInitialized)
            throw new AssertionError("clientInitialization() already called");

        // Some unit tests require this :(
        if (daemonInitialized)
            return;
        daemonInitialized = true;

        setConfig(config.get());
        applyAll();
        AuthConfig.applyAuth();
    }

    /**
     * Equivalent to {@link #toolInitialization(boolean) toolInitialization(true)}.
     */
    public static void toolInitialization()
    {
        toolInitialization(true);
    }

    /**
     * Initializes this class as a tool, which means that the configuration is loaded
     * using {@link #loadConfig()} and all non-daemon configuration parts will be setup.
     *
     * @param failIfDaemonOrClient if {@code true} and a call to {@link #daemonInitialization()} or
     *                             {@link #clientInitialization()} has been performed before, an
     *                             {@link AssertionError} will be thrown.
     */
    public static void toolInitialization(boolean failIfDaemonOrClient)
    {
        if (!failIfDaemonOrClient && (daemonInitialized || clientInitialized))
        {
            return;
        }
        else
        {
            if (daemonInitialized)
                throw new AssertionError("daemonInitialization() already called");
            if (clientInitialized)
                throw new AssertionError("clientInitialization() already called");
        }

        if (toolInitialized)
            return;
        toolInitialized = true;

        setConfig(loadConfig());

        applySimpleConfig();

        applyPartitioner();

        applySnitch();

        applyEncryptionContext();
    }

    /**
     * Equivalent to {@link #clientInitialization(boolean) clientInitialization(true)}.
     */
    public static void clientInitialization()
    {
        clientInitialization(true);
    }

    /**
     * Initializes this class as a client, which means that just an empty configuration will
     * be used.
     *
     * @param failIfDaemonOrTool if {@code true} and a call to {@link #daemonInitialization()} or
     *                           {@link #toolInitialization()} has been performed before, an
     *                           {@link AssertionError} will be thrown.
     */
    public static void clientInitialization(boolean failIfDaemonOrTool)
    {
        if (!failIfDaemonOrTool && (daemonInitialized || toolInitialized))
        {
            return;
        }
        else
        {
            if (daemonInitialized)
                throw new AssertionError("daemonInitialization() already called");
            if (toolInitialized)
                throw new AssertionError("toolInitialization() already called");
        }

        if (clientInitialized)
            return;
        clientInitialized = true;

        Config.setClientMode(true);
        conf = new Config();
        diskOptimizationStrategy = new SpinningDiskOptimizationStrategy();
    }

    public static boolean isClientInitialized()
    {
        return clientInitialized;
    }

    public static boolean isToolInitialized()
    {
        return toolInitialized;
    }

    public static boolean isClientOrToolInitialized()
    {
        return clientInitialized || toolInitialized;
    }

    public static boolean isDaemonInitialized()
    {
        return daemonInitialized;
    }

    public static Config getRawConfig()
    {
        return conf;
    }

    @VisibleForTesting
    public static Config loadConfig() throws ConfigurationException
    {
        if (Config.getOverrideLoadConfig() != null)
            return Config.getOverrideLoadConfig().get();

        String loaderClass = System.getProperty(Config.PROPERTY_PREFIX + "config.loader");
        ConfigurationLoader loader = loaderClass == null
                                     ? new YamlConfigurationLoader()
                                     : FBUtilities.construct(loaderClass, "configuration loading");
        Config config = loader.loadConfig();

        if (!hasLoggedConfig)
        {
            hasLoggedConfig = true;
            Config.log(config);
        }

        return config;
    }

    private static InetAddress getNetworkInterfaceAddress(String intf, String configName, boolean preferIPv6) throws ConfigurationException
    {
        try
        {
            NetworkInterface ni = NetworkInterface.getByName(intf);
            if (ni == null)
                throw new ConfigurationException("Configured " + configName + " \"" + intf + "\" could not be found", false);
            Enumeration<InetAddress> addrs = ni.getInetAddresses();
            if (!addrs.hasMoreElements())
                throw new ConfigurationException("Configured " + configName + " \"" + intf + "\" was found, but had no addresses", false);

            /*
             * Try to return the first address of the preferred type, otherwise return the first address
             */
            InetAddress retval = null;
            while (addrs.hasMoreElements())
            {
                InetAddress temp = addrs.nextElement();
                if (preferIPv6 && temp instanceof Inet6Address) return temp;
                if (!preferIPv6 && temp instanceof Inet4Address) return temp;
                if (retval == null) retval = temp;
            }
            return retval;
        }
        catch (SocketException e)
        {
            throw new ConfigurationException("Configured " + configName + " \"" + intf + "\" caused an exception", e);
        }
    }

    private static void setConfig(Config config)
    {
        conf = config;
    }

    private static void applyAll() throws ConfigurationException
    {
        //InetAddressAndPort cares that applySimpleConfig runs first
        applySimpleConfig();

        applyPartitioner();

        applyAddressConfig();

        applySnitch();

        applyTokensConfig();

        applySeedProvider();

        applyEncryptionContext();

        applySslContext();
    }

    private static void applySimpleConfig()
    {
        //Doing this first before all other things in case other pieces of config want to construct
        //InetAddressAndPort and get the right defaults
        InetAddressAndPort.initializeDefaultPort(getStoragePort());

        if (conf.commitlog_sync == null)
        {
            throw new ConfigurationException("Missing required directive CommitLogSync", false);
        }

        if (conf.commitlog_sync == Config.CommitLogSync.batch)
        {
            if (conf.commitlog_sync_period_in_ms != 0)
            {
                throw new ConfigurationException("Batch sync specified, but commitlog_sync_period_in_ms found. Only specify commitlog_sync_batch_window_in_ms when using batch sync", false);
            }
            logger.debug("Syncing log with batch mode");
        }
        else if (conf.commitlog_sync == CommitLogSync.group)
        {
            if (Double.isNaN(conf.commitlog_sync_group_window_in_ms) || conf.commitlog_sync_group_window_in_ms <= 0d)
            {
                throw new ConfigurationException("Missing value for commitlog_sync_group_window_in_ms: positive double value expected.", false);
            }
            else if (conf.commitlog_sync_period_in_ms != 0)
            {
                throw new ConfigurationException("Group sync specified, but commitlog_sync_period_in_ms found. Only specify commitlog_sync_group_window_in_ms when using group sync", false);
            }
            logger.debug("Syncing log with a group window of {}", conf.commitlog_sync_period_in_ms);
        }
        else
        {
            if (conf.commitlog_sync_period_in_ms <= 0)
            {
                throw new ConfigurationException("Missing value for commitlog_sync_period_in_ms: positive integer expected", false);
            }
            else if (!Double.isNaN(conf.commitlog_sync_batch_window_in_ms))
            {
                throw new ConfigurationException("commitlog_sync_period_in_ms specified, but commitlog_sync_batch_window_in_ms found.  Only specify commitlog_sync_period_in_ms when using periodic sync.", false);
            }
            logger.debug("Syncing log with a period of {}", conf.commitlog_sync_period_in_ms);
        }

        /* evaluate the DiskAccessMode Config directive, which also affects indexAccessMode selection */
        if (conf.disk_access_mode == Config.DiskAccessMode.auto)
        {
            conf.disk_access_mode = hasLargeAddressSpace() ? Config.DiskAccessMode.mmap : Config.DiskAccessMode.standard;
            indexAccessMode = conf.disk_access_mode;
            logger.info("DiskAccessMode 'auto' determined to be {}, indexAccessMode is {}", conf.disk_access_mode, indexAccessMode);
        }
        else if (conf.disk_access_mode == Config.DiskAccessMode.mmap_index_only)
        {
            conf.disk_access_mode = Config.DiskAccessMode.standard;
            indexAccessMode = Config.DiskAccessMode.mmap;
            logger.info("DiskAccessMode is {}, indexAccessMode is {}", conf.disk_access_mode, indexAccessMode);
        }
        else
        {
            indexAccessMode = conf.disk_access_mode;
            logger.info("DiskAccessMode is {}, indexAccessMode is {}", conf.disk_access_mode, indexAccessMode);
        }

        if (conf.gc_warn_threshold_in_ms < 0)
        {
            throw new ConfigurationException("gc_warn_threshold_in_ms must be a positive integer");
        }

        /* phi convict threshold for FailureDetector */
        if (conf.phi_convict_threshold < 5 || conf.phi_convict_threshold > 16)
        {
            throw new ConfigurationException("phi_convict_threshold must be between 5 and 16, but was " + conf.phi_convict_threshold, false);
        }

        /* Thread per pool */
        if (conf.concurrent_reads < 2)
        {
            throw new ConfigurationException("concurrent_reads must be at least 2, but was " + conf.concurrent_reads, false);
        }

        if (conf.concurrent_writes < 2 && System.getProperty("cassandra.test.fail_mv_locks_count", "").isEmpty())
        {
            throw new ConfigurationException("concurrent_writes must be at least 2, but was " + conf.concurrent_writes, false);
        }

        if (conf.concurrent_counter_writes < 2)
            throw new ConfigurationException("concurrent_counter_writes must be at least 2, but was " + conf.concurrent_counter_writes, false);

        if (conf.concurrent_replicates != null)
            logger.warn("concurrent_replicates has been deprecated and should be removed from cassandra.yaml");

        if (conf.networking_cache_size_in_mb == null)
            conf.networking_cache_size_in_mb = Math.min(128, (int) (Runtime.getRuntime().maxMemory() / (16 * 1048576)));

        if (conf.file_cache_size_in_mb == null)
            conf.file_cache_size_in_mb = Math.min(512, (int) (Runtime.getRuntime().maxMemory() / (4 * 1048576)));

        // round down for SSDs and round up for spinning disks
        if (conf.file_cache_round_up == null)
            conf.file_cache_round_up = conf.disk_optimization_strategy == Config.DiskOptimizationStrategy.spinning;

        if (conf.memtable_offheap_space_in_mb == null)
            conf.memtable_offheap_space_in_mb = (int) (Runtime.getRuntime().maxMemory() / (4 * 1048576));
        if (conf.memtable_offheap_space_in_mb < 0)
            throw new ConfigurationException("memtable_offheap_space_in_mb must be positive, but was " + conf.memtable_offheap_space_in_mb, false);
        // for the moment, we default to twice as much on-heap space as off-heap, as heap overhead is very large
        if (conf.memtable_heap_space_in_mb == null)
            conf.memtable_heap_space_in_mb = (int) (Runtime.getRuntime().maxMemory() / (4 * 1048576));
        if (conf.memtable_heap_space_in_mb <= 0)
            throw new ConfigurationException("memtable_heap_space_in_mb must be positive, but was " + conf.memtable_heap_space_in_mb, false);
        logger.info("Global memtable on-heap threshold is enabled at {}MB", conf.memtable_heap_space_in_mb);
        if (conf.memtable_offheap_space_in_mb == 0)
            logger.info("Global memtable off-heap threshold is disabled, HeapAllocator will be used instead");
        else
            logger.info("Global memtable off-heap threshold is enabled at {}MB", conf.memtable_offheap_space_in_mb);

        if (conf.repair_session_max_tree_depth != null)
        {
            logger.warn("repair_session_max_tree_depth has been deprecated and should be removed from cassandra.yaml. Use repair_session_space_in_mb instead");
            if (conf.repair_session_max_tree_depth < 10)
                throw new ConfigurationException("repair_session_max_tree_depth should not be < 10, but was " + conf.repair_session_max_tree_depth);
            if (conf.repair_session_max_tree_depth > 20)
                logger.warn("repair_session_max_tree_depth of " + conf.repair_session_max_tree_depth + " > 20 could lead to excessive memory usage");
        }
        else
        {
            conf.repair_session_max_tree_depth = 20;
        }

        if (conf.repair_session_space_in_mb == null)
            conf.repair_session_space_in_mb = Math.max(1, (int) (Runtime.getRuntime().maxMemory() / (16 * 1048576)));

        if (conf.repair_session_space_in_mb < 1)
            throw new ConfigurationException("repair_session_space_in_mb must be > 0, but was " + conf.repair_session_space_in_mb);
        else if (conf.repair_session_space_in_mb > (int) (Runtime.getRuntime().maxMemory() / (4 * 1048576)))
            logger.warn("A repair_session_space_in_mb of " + conf.repair_session_space_in_mb + " megabytes is likely to cause heap pressure");

        checkForLowestAcceptedTimeouts(conf);

        checkValidForByteConversion(conf.native_transport_max_frame_size_in_mb,
                                    "native_transport_max_frame_size_in_mb", ByteUnit.MEBI_BYTES);

        checkValidForByteConversion(conf.column_index_size_in_kb,
                                    "column_index_size_in_kb", ByteUnit.KIBI_BYTES);

        checkValidForByteConversion(conf.column_index_cache_size_in_kb,
                                    "column_index_cache_size_in_kb", ByteUnit.KIBI_BYTES);

        checkValidForByteConversion(conf.batch_size_warn_threshold_in_kb,
                                    "batch_size_warn_threshold_in_kb", ByteUnit.KIBI_BYTES);

        if (conf.native_transport_max_negotiable_protocol_version != null)
            logger.warn("The configuration option native_transport_max_negotiable_protocol_version has been deprecated " +
                        "and should be removed from cassandra.yaml as it has no longer has any effect.");

        // if data dirs, commitlog dir, or saved caches dir are set in cassandra.yaml, use that.  Otherwise,
        // use -Dcassandra.storagedir (set in cassandra-env.sh) as the parent dir for data/, commitlog/, and saved_caches/
        if (conf.commitlog_directory == null)
        {
            conf.commitlog_directory = storagedirFor("commitlog");
        }

        if (conf.hints_directory == null)
        {
            conf.hints_directory = storagedirFor("hints");
        }

        if (conf.native_transport_max_concurrent_requests_in_bytes <= 0)
        {
            conf.native_transport_max_concurrent_requests_in_bytes = Runtime.getRuntime().maxMemory() / 10;
        }

        if (conf.native_transport_max_concurrent_requests_in_bytes_per_ip <= 0)
        {
            conf.native_transport_max_concurrent_requests_in_bytes_per_ip = Runtime.getRuntime().maxMemory() / 40;
        }

        if (conf.commitlog_total_space_in_mb == null)
        {
            final int preferredSizeInMB = 8192;
            try
            {
                // use 1/4 of available space.  See discussion on #10013 and #10199
                final long totalSpaceInBytes = guessFileStore(conf.commitlog_directory).getTotalSpace();
                conf.commitlog_total_space_in_mb = calculateDefaultSpaceInMB("commitlog",
                                                                             conf.commitlog_directory,
                                                                             "commitlog_total_space_in_mb",
                                                                             preferredSizeInMB,
                                                                             totalSpaceInBytes, 1, 4);

            }
            catch (IOException e)
            {
                logger.debug("Error checking disk space", e);
                throw new ConfigurationException(String.format("Unable to check disk space available to '%s'. Perhaps the Cassandra user does not have the necessary permissions",
                                                               conf.commitlog_directory), e);
            }
        }

        if (conf.cdc_enabled)
        {
            // Windows memory-mapped CommitLog files is incompatible with CDC as we hard-link files in cdc_raw. Confirm we don't have both enabled.
            if (FBUtilities.isWindows && conf.commitlog_compression == null)
                throw new ConfigurationException("Cannot enable cdc on Windows with uncompressed commitlog.");

            if (conf.cdc_raw_directory == null)
            {
                conf.cdc_raw_directory = storagedirFor("cdc_raw");
            }

            if (conf.cdc_total_space_in_mb == 0)
            {
                final int preferredSizeInMB = 4096;
                try
                {
                    // use 1/8th of available space.  See discussion on #10013 and #10199 on the CL, taking half that for CDC
                    final long totalSpaceInBytes = guessFileStore(conf.cdc_raw_directory).getTotalSpace();
                    conf.cdc_total_space_in_mb = calculateDefaultSpaceInMB("cdc",
                                                                           conf.cdc_raw_directory,
                                                                           "cdc_total_space_in_mb",
                                                                           preferredSizeInMB,
                                                                           totalSpaceInBytes, 1, 8);
                }
                catch (IOException e)
                {
                    logger.debug("Error checking disk space", e);
                    throw new ConfigurationException(String.format("Unable to check disk space available to '%s'. Perhaps the Cassandra user does not have the necessary permissions",
                                                                   conf.cdc_raw_directory), e);
                }
            }

            logger.info("cdc_enabled is true. Starting casssandra node with Change-Data-Capture enabled.");
        }

        if (conf.saved_caches_directory == null)
        {
            conf.saved_caches_directory = storagedirFor("saved_caches");
        }
        if (conf.data_file_directories == null || conf.data_file_directories.length == 0)
        {
            conf.data_file_directories = new String[]{ storagedir("data_file_directories") + File.separator + "data" };
        }

        long dataFreeBytes = 0;
        /* data file and commit log directories. they get created later, when they're needed. */
        for (String datadir : conf.data_file_directories)
        {
            if (datadir == null)
                throw new ConfigurationException("data_file_directories must not contain empty entry", false);
            if (datadir.equals(conf.local_system_data_file_directory))
                throw new ConfigurationException("local_system_data_file_directory must not be the same as any data_file_directories", false);
            if (datadir.equals(conf.commitlog_directory))
                throw new ConfigurationException("commitlog_directory must not be the same as any data_file_directories", false);
            if (datadir.equals(conf.hints_directory))
                throw new ConfigurationException("hints_directory must not be the same as any data_file_directories", false);
            if (datadir.equals(conf.saved_caches_directory))
                throw new ConfigurationException("saved_caches_directory must not be the same as any data_file_directories", false);

            dataFreeBytes = saturatedSum(dataFreeBytes, getUnallocatedSpace(datadir));
        }
        if (dataFreeBytes < 64 * ONE_GB) // 64 GB
            logger.warn("Only {} free across all data volumes. Consider adding more capacity to your cluster or removing obsolete snapshots",
                        FBUtilities.prettyPrintMemory(dataFreeBytes));

        if (conf.local_system_data_file_directory != null)
        {
            if (conf.local_system_data_file_directory.equals(conf.commitlog_directory))
                throw new ConfigurationException("local_system_data_file_directory must not be the same as the commitlog_directory", false);
            if (conf.local_system_data_file_directory.equals(conf.saved_caches_directory))
                throw new ConfigurationException("local_system_data_file_directory must not be the same as the saved_caches_directory", false);
            if (conf.local_system_data_file_directory.equals(conf.hints_directory))
                throw new ConfigurationException("local_system_data_file_directory must not be the same as the hints_directory", false);

            long freeBytes = getUnallocatedSpace(conf.local_system_data_file_directory);

            if (freeBytes < ONE_GB)
                logger.warn("Only {} free in the system data volume. Consider adding more capacity or removing obsolete snapshots",
                            FBUtilities.prettyPrintMemory(freeBytes));
        }

        if (conf.commitlog_directory.equals(conf.saved_caches_directory))
            throw new ConfigurationException("saved_caches_directory must not be the same as the commitlog_directory", false);
        if (conf.commitlog_directory.equals(conf.hints_directory))
            throw new ConfigurationException("hints_directory must not be the same as the commitlog_directory", false);
        if (conf.hints_directory.equals(conf.saved_caches_directory))
            throw new ConfigurationException("saved_caches_directory must not be the same as the hints_directory", false);

        if (conf.memtable_flush_writers == 0)
        {
            conf.memtable_flush_writers = conf.data_file_directories.length == 1 ? 2 : 1;
        }

        if (conf.memtable_flush_writers < 1)
            throw new ConfigurationException("memtable_flush_writers must be at least 1, but was " + conf.memtable_flush_writers, false);

        if (conf.memtable_cleanup_threshold == null)
        {
            conf.memtable_cleanup_threshold = (float) (1.0 / (1 + conf.memtable_flush_writers));
        }
        else
        {
            logger.warn("memtable_cleanup_threshold has been deprecated and should be removed from cassandra.yaml");
        }

        if (conf.memtable_cleanup_threshold < 0.01f)
            throw new ConfigurationException("memtable_cleanup_threshold must be >= 0.01, but was " + conf.memtable_cleanup_threshold, false);
        if (conf.memtable_cleanup_threshold > 0.99f)
            throw new ConfigurationException("memtable_cleanup_threshold must be <= 0.99, but was " + conf.memtable_cleanup_threshold, false);
        if (conf.memtable_cleanup_threshold < 0.1f)
            logger.warn("memtable_cleanup_threshold is set very low [{}], which may cause performance degradation", conf.memtable_cleanup_threshold);

        if (conf.concurrent_compactors == null)
            conf.concurrent_compactors = Math.min(8, Math.max(2, Math.min(FBUtilities.getAvailableProcessors(), conf.data_file_directories.length)));

        if (conf.concurrent_compactors <= 0)
            throw new ConfigurationException("concurrent_compactors should be strictly greater than 0, but was " + conf.concurrent_compactors, false);

        applyConcurrentValidations(conf);
        applyRepairCommandPoolSize(conf);

        if (conf.concurrent_materialized_view_builders <= 0)
            throw new ConfigurationException("concurrent_materialized_view_builders should be strictly greater than 0, but was " + conf.concurrent_materialized_view_builders, false);

        if (conf.num_tokens != null && conf.num_tokens > MAX_NUM_TOKENS)
            throw new ConfigurationException(String.format("A maximum number of %d tokens per node is supported", MAX_NUM_TOKENS), false);

        try
        {
            // if prepared_statements_cache_size_mb option was set to "auto" then size of the cache should be "max(1/256 of Heap (in MB), 10MB)"
            preparedStatementsCacheSizeInMB = (conf.prepared_statements_cache_size_mb == null)
                                              ? Math.max(10, (int) (Runtime.getRuntime().maxMemory() / 1024 / 1024 / 256))
                                              : conf.prepared_statements_cache_size_mb;

            if (preparedStatementsCacheSizeInMB <= 0)
                throw new NumberFormatException(); // to escape duplicating error message

            // we need this assignment for the Settings virtual table - CASSANDRA-17734
            conf.prepared_statements_cache_size_mb = preparedStatementsCacheSizeInMB;
        }
        catch (NumberFormatException e)
        {
            throw new ConfigurationException("prepared_statements_cache_size_mb option was set incorrectly to '"
                                             + conf.prepared_statements_cache_size_mb + "', supported values are <integer> >= 0.", false);
        }

        try
        {
            // if key_cache_size_in_mb option was set to "auto" then size of the cache should be "min(5% of Heap (in MB), 100MB)
            keyCacheSizeInMB = (conf.key_cache_size_in_mb == null)
                               ? Math.min(Math.max(1, (int) (Runtime.getRuntime().totalMemory() * 0.05 / 1024 / 1024)), 100)
                               : conf.key_cache_size_in_mb;

            if (keyCacheSizeInMB < 0)
                throw new NumberFormatException(); // to escape duplicating error message

            // we need this assignment for the Settings Virtual Table - CASSANDRA-17734
            conf.key_cache_size_in_mb = keyCacheSizeInMB;
        }
        catch (NumberFormatException e)
        {
            throw new ConfigurationException("key_cache_size_in_mb option was set incorrectly to '"
                                             + conf.key_cache_size_in_mb + "', supported values are <integer> >= 0.", false);
        }

        try
        {
            // if counter_cache_size_in_mb option was set to "auto" then size of the cache should be "min(2.5% of Heap (in MB), 50MB)
            counterCacheSizeInMB = (conf.counter_cache_size_in_mb == null)
                                   ? Math.min(Math.max(1, (int) (Runtime.getRuntime().totalMemory() * 0.025 / 1024 / 1024)), 50)
                                   : conf.counter_cache_size_in_mb;

            if (counterCacheSizeInMB < 0)
                throw new NumberFormatException(); // to escape duplicating error message
        }
        catch (NumberFormatException e)
        {
            throw new ConfigurationException("counter_cache_size_in_mb option was set incorrectly to '"
                                             + conf.counter_cache_size_in_mb + "', supported values are <integer> >= 0.", false);
        }

        // we need this assignment for the Settings virtual table - CASSANDRA-17735
        conf.counter_cache_size_in_mb = counterCacheSizeInMB;

        // if set to empty/"auto" then use 5% of Heap size
        indexSummaryCapacityInMB = (conf.index_summary_capacity_in_mb == null)
                                   ? Math.max(1, (int) (Runtime.getRuntime().totalMemory() * 0.05 / 1024 / 1024))
                                   : conf.index_summary_capacity_in_mb;

        if (indexSummaryCapacityInMB < 0)
            throw new ConfigurationException("index_summary_capacity_in_mb option was set incorrectly to '"
                                             + conf.index_summary_capacity_in_mb + "', it should be a non-negative integer.", false);

        // we need this assignment for the Settings virtual table - CASSANDRA-17735
        conf.index_summary_capacity_in_mb = indexSummaryCapacityInMB;

        if (conf.user_defined_function_fail_timeout < 0)
            throw new ConfigurationException("user_defined_function_fail_timeout must not be negative", false);
        if (conf.user_defined_function_warn_timeout < 0)
            throw new ConfigurationException("user_defined_function_warn_timeout must not be negative", false);

        if (conf.user_defined_function_fail_timeout < conf.user_defined_function_warn_timeout)
            throw new ConfigurationException("user_defined_function_warn_timeout must less than user_defined_function_fail_timeout", false);

        if (!conf.allow_insecure_udfs && !conf.enable_user_defined_functions_threads)
            throw new ConfigurationException("To be able to set enable_user_defined_functions_threads: false you need to set allow_insecure_udfs: true - this is an unsafe configuration and is not recommended.");

        if (conf.allow_extra_insecure_udfs)
            logger.warn("Allowing java.lang.System.* access in UDFs is dangerous and not recommended. Set allow_extra_insecure_udfs: false to disable.");

        if(conf.enable_scripted_user_defined_functions)
            logger.warn("JavaScript user-defined functions have been deprecated. You can still use them but the plan is to remove them in the next major version. For more information - CASSANDRA-17280");

        if (conf.commitlog_segment_size_in_mb <= 0)
            throw new ConfigurationException("commitlog_segment_size_in_mb must be positive, but was "
                    + conf.commitlog_segment_size_in_mb, false);
        else if (conf.commitlog_segment_size_in_mb >= 2048)
            throw new ConfigurationException("commitlog_segment_size_in_mb must be smaller than 2048, but was "
                    + conf.commitlog_segment_size_in_mb, false);

        if (conf.max_mutation_size_in_kb == null)
            conf.max_mutation_size_in_kb = conf.commitlog_segment_size_in_mb * 1024 / 2;
        else if (conf.commitlog_segment_size_in_mb * 1024 < 2 * conf.max_mutation_size_in_kb)
            throw new ConfigurationException("commitlog_segment_size_in_mb must be at least twice the size of max_mutation_size_in_kb / 1024", false);

        // native transport encryption options
        if (conf.client_encryption_options != null)
        {
            conf.client_encryption_options.applyConfig();

            if (conf.native_transport_port_ssl != null
                && conf.native_transport_port_ssl != conf.native_transport_port
                && conf.client_encryption_options.tlsEncryptionPolicy() == EncryptionOptions.TlsEncryptionPolicy.UNENCRYPTED)
            {
                throw new ConfigurationException("Encryption must be enabled in client_encryption_options for native_transport_port_ssl", false);
            }
        }

        if (conf.snapshot_links_per_second < 0)
            throw new ConfigurationException("snapshot_links_per_second must be >= 0");

        if (conf.max_value_size_in_mb <= 0)
            throw new ConfigurationException("max_value_size_in_mb must be positive", false);
        else if (conf.max_value_size_in_mb >= 2048)
            throw new ConfigurationException("max_value_size_in_mb must be smaller than 2048, but was "
                    + conf.max_value_size_in_mb, false);

        switch (conf.disk_optimization_strategy)
        {
            case ssd:
                diskOptimizationStrategy = new SsdDiskOptimizationStrategy(conf.disk_optimization_page_cross_chance);
                break;
            case spinning:
                diskOptimizationStrategy = new SpinningDiskOptimizationStrategy();
                break;
        }

        if (conf.server_encryption_options != null)
        {
            conf.server_encryption_options.applyConfig();

            if (conf.server_encryption_options.enable_legacy_ssl_storage_port &&
                conf.server_encryption_options.tlsEncryptionPolicy() == EncryptionOptions.TlsEncryptionPolicy.UNENCRYPTED)
            {
                throw new ConfigurationException("enable_legacy_ssl_storage_port is true (enabled) with internode encryption disabled (none). Enable encryption or disable the legacy ssl storage port.");
            }
        }
        Integer maxMessageSize = conf.internode_max_message_size_in_bytes;
        if (maxMessageSize != null)
        {
            if (maxMessageSize > conf.internode_application_receive_queue_reserve_endpoint_capacity_in_bytes)
                throw new ConfigurationException("internode_max_message_size_in_mb must no exceed internode_application_receive_queue_reserve_endpoint_capacity_in_bytes", false);

            if (maxMessageSize > conf.internode_application_receive_queue_reserve_global_capacity_in_bytes)
                throw new ConfigurationException("internode_max_message_size_in_mb must no exceed internode_application_receive_queue_reserve_global_capacity_in_bytes", false);

            if (maxMessageSize > conf.internode_application_send_queue_reserve_endpoint_capacity_in_bytes)
                throw new ConfigurationException("internode_max_message_size_in_mb must no exceed internode_application_send_queue_reserve_endpoint_capacity_in_bytes", false);

            if (maxMessageSize > conf.internode_application_send_queue_reserve_global_capacity_in_bytes)
                throw new ConfigurationException("internode_max_message_size_in_mb must no exceed internode_application_send_queue_reserve_global_capacity_in_bytes", false);
        }
        else
        {
            conf.internode_max_message_size_in_bytes =
                Math.min(conf.internode_application_receive_queue_reserve_endpoint_capacity_in_bytes,
                         conf.internode_application_send_queue_reserve_endpoint_capacity_in_bytes);
        }

        validateMaxConcurrentAutoUpgradeTasksConf(conf.max_concurrent_automatic_sstable_upgrades);
    }

    @VisibleForTesting
    static void applyConcurrentValidations(Config config)
    {
        logger.warn("[CTEST][GET-PARAM] " + "concurrent_validations" ); //CTEST
        logger.warn("[CTEST][GET-PARAM] " + "concurrent_compactors" ); //CTEST
        if (config.concurrent_validations < 1)
        {
            logger.warn("[CTEST][SET-PARAM] " + "concurrent_compactors" + getStackTrace()); //CTEST
            config.concurrent_validations = config.concurrent_compactors;
        }
        else if (config.concurrent_validations > config.concurrent_compactors && !allowUnlimitedConcurrentValidations)
        {
            throw new ConfigurationException("To set concurrent_validations > concurrent_compactors, " +
                                             "set the system property cassandra.allow_unlimited_concurrent_validations=true");
        }
    }

    @VisibleForTesting
    static void applyRepairCommandPoolSize(Config config)
    {
        if (config.repair_command_pool_size < 1) {
            logger.warn("[CTEST][SET-PARAM] " + "concurrent_validations" + getStackTrace()); //CTEST
            config.repair_command_pool_size = config.concurrent_validations;
        }
    }

    private static String storagedirFor(String type)
    {
        return storagedir(type + "_directory") + File.separator + type;
    }

    private static String storagedir(String errMsgType)
    {
        String storagedir = System.getProperty(Config.PROPERTY_PREFIX + "storagedir", null);
        if (storagedir == null)
            throw new ConfigurationException(errMsgType + " is missing and -Dcassandra.storagedir is not set", false);
        return storagedir;
    }

    static int calculateDefaultSpaceInMB(String type, String path, String setting, int preferredSizeInMB, long totalSpaceInBytes, long totalSpaceNumerator, long totalSpaceDenominator)
    {
        final long totalSizeInMB = totalSpaceInBytes / ONE_MB;
        final int minSizeInMB = Ints.saturatedCast(totalSpaceNumerator * totalSizeInMB / totalSpaceDenominator);

        if (minSizeInMB < preferredSizeInMB)
        {
            logger.warn("Small {} volume detected at '{}'; setting {} to {}.  You can override this in cassandra.yaml",
                        type, path, setting, minSizeInMB);
            return minSizeInMB;
        }
        else
        {
            return preferredSizeInMB;
        }
    }

    public static void applyAddressConfig() throws ConfigurationException
    {
        applyAddressConfig(conf);
    }

    public static void applyAddressConfig(Config config) throws ConfigurationException
    {
        listenAddress = null;
        rpcAddress = null;
        broadcastAddress = null;
        broadcastRpcAddress = null;

        /* Local IP, hostname or interface to bind services to */
        logger.warn("[CTEST][GET-PARAM] " + "listen_address" ); //CTEST
        logger.warn("[CTEST][GET-PARAM] " + "listen_interface" ); //CTEST
        if (config.listen_address != null && config.listen_interface != null)
        {
            throw new ConfigurationException("Set listen_address OR listen_interface, not both", false);
        }
        else if (config.listen_address != null)
        {
            try
            {
                listenAddress = InetAddress.getByName(config.listen_address);
            }
            catch (UnknownHostException e)
            {
                throw new ConfigurationException("Unknown listen_address '" + config.listen_address + '\'', false);
            }

            if (listenAddress.isAnyLocalAddress())
                throw new ConfigurationException("listen_address cannot be a wildcard address (" + config.listen_address + ")!", false);
        }
        else if (config.listen_interface != null)
        {
            listenAddress = getNetworkInterfaceAddress(config.listen_interface, "listen_interface", config.listen_interface_prefer_ipv6);
        }

        /* Gossip Address to broadcast */
        logger.warn("[CTEST][GET-PARAM] " + "broadcast_address" ); //CTEST
        if (config.broadcast_address != null)
        {
            try
            {
                broadcastAddress = InetAddress.getByName(config.broadcast_address);
            }
            catch (UnknownHostException e)
            {
                throw new ConfigurationException("Unknown broadcast_address '" + config.broadcast_address + '\'', false);
            }

            if (broadcastAddress.isAnyLocalAddress())
                throw new ConfigurationException("broadcast_address cannot be a wildcard address (" + config.broadcast_address + ")!", false);
        }

        /* Local IP, hostname or interface to bind RPC server to */
        logger.warn("[CTEST][GET-PARAM] " + "rpc_address" ); //CTEST
        logger.warn("[CTEST][GET-PARAM] " + "rpc_interface" ); //CTEST
        if (config.rpc_address != null && config.rpc_interface != null)
        {
            throw new ConfigurationException("Set rpc_address OR rpc_interface, not both", false);
        }
        else if (config.rpc_address != null)
        {
            try
            {
                rpcAddress = InetAddress.getByName(config.rpc_address);
            }
            catch (UnknownHostException e)
            {
                throw new ConfigurationException("Unknown host in rpc_address " + config.rpc_address, false);
            }
        }
        else if (config.rpc_interface != null)
        {
            rpcAddress = getNetworkInterfaceAddress(config.rpc_interface, "rpc_interface", config.rpc_interface_prefer_ipv6);
        }
        else
        {
            rpcAddress = FBUtilities.getJustLocalAddress();
        }

        /* RPC address to broadcast */
        logger.warn("[CTEST][GET-PARAM] " + "broadcast_rpc_address" ); //CTEST
        if (config.broadcast_rpc_address != null)
        {
            try
            {
                broadcastRpcAddress = InetAddress.getByName(config.broadcast_rpc_address);
            }
            catch (UnknownHostException e)
            {
                throw new ConfigurationException("Unknown broadcast_rpc_address '" + config.broadcast_rpc_address + '\'', false);
            }

            if (broadcastRpcAddress.isAnyLocalAddress())
                throw new ConfigurationException("broadcast_rpc_address cannot be a wildcard address (" + config.broadcast_rpc_address + ")!", false);
        }
        else
        {
            if (rpcAddress.isAnyLocalAddress())
                throw new ConfigurationException("If rpc_address is set to a wildcard address (" + config.rpc_address + "), then " +
                                                 "you must set broadcast_rpc_address to a value other than " + config.rpc_address, false);
        }
    }

    public static void applyEncryptionContext()
    {
        // always attempt to load the cipher factory, as we could be in the situation where the user has disabled encryption,
        // but has existing commitlogs and sstables on disk that are still encrypted (and still need to be read)
        logger.warn("[CTEST][GET-PARAM] " + "transparent_data_encryption_options" ); //CTEST
        encryptionContext = new EncryptionContext(conf.transparent_data_encryption_options);
    }

    public static void applySslContext()
    {
        try
        {
            logger.warn("[CTEST][GET-PARAM] " + "server_encryption_options" ); //CTEST
            SSLFactory.validateSslContext("Internode messaging", conf.server_encryption_options, true, true);
            logger.warn("[CTEST][GET-PARAM] " + "client_encryption_options" ); //CTEST
            logger.warn("[CTEST][GET-PARAM] " + "client_encryption_options.require_client_auth" ); //CTEST
            SSLFactory.validateSslContext("Native transport", conf.client_encryption_options, conf.client_encryption_options.require_client_auth, true);
            SSLFactory.initHotReloading(conf.server_encryption_options, conf.client_encryption_options, false);
        }
        catch (IOException e)
        {
            throw new ConfigurationException("Failed to initialize SSL", e);
        }
    }

    public static void applySeedProvider()
    {
        // load the seeds for node contact points
        if (conf.seed_provider == null)
        {
            throw new ConfigurationException("seeds configuration is missing; a minimum of one seed is required.", false);
        }
        try
        {
            logger.warn("[CTEST][GET-PARAM] " + "seed_provider.parameters" ); //CTEST
            Class<?> seedProviderClass = Class.forName(conf.seed_provider.class_name);
            seedProvider = (SeedProvider)seedProviderClass.getConstructor(Map.class).newInstance(conf.seed_provider.parameters);
        }
        // there are about 5 checked exceptions that could be thrown here.
        catch (Exception e)
        {
            throw new ConfigurationException(e.getMessage() + "\nFatal configuration error; unable to start server.  See log for stacktrace.", true);
        }
        if (seedProvider.getSeeds().size() == 0)
            throw new ConfigurationException("The seed provider lists no seeds.", false);
    }

    @VisibleForTesting
    static void checkForLowestAcceptedTimeouts(Config conf)
    {
        if(conf.read_request_timeout_in_ms < LOWEST_ACCEPTED_TIMEOUT)
        {
           logInfo("read_request_timeout_in_ms", conf.read_request_timeout_in_ms, LOWEST_ACCEPTED_TIMEOUT);
           conf.read_request_timeout_in_ms = LOWEST_ACCEPTED_TIMEOUT;
            logger.warn("[CTEST][SET-PARAM] " + "read_request_timeout_in_ms" + getStackTrace()); //CTEST
        }

        if(conf.range_request_timeout_in_ms < LOWEST_ACCEPTED_TIMEOUT)
        {
           logInfo("range_request_timeout_in_ms", conf.range_request_timeout_in_ms, LOWEST_ACCEPTED_TIMEOUT);
           conf.range_request_timeout_in_ms = LOWEST_ACCEPTED_TIMEOUT;
            logger.warn("[CTEST][SET-PARAM] " + "range_request_timeout_in_ms" + getStackTrace()); //CTEST
        }

        if(conf.request_timeout_in_ms < LOWEST_ACCEPTED_TIMEOUT)
        {
           logInfo("request_timeout_in_ms", conf.request_timeout_in_ms, LOWEST_ACCEPTED_TIMEOUT);
           conf.request_timeout_in_ms = LOWEST_ACCEPTED_TIMEOUT;
            logger.warn("[CTEST][SET-PARAM] " + "request_timeout_in_ms" + getStackTrace()); //CTEST
        }

        if(conf.write_request_timeout_in_ms < LOWEST_ACCEPTED_TIMEOUT)
        {
           logInfo("write_request_timeout_in_ms", conf.write_request_timeout_in_ms, LOWEST_ACCEPTED_TIMEOUT);
           conf.write_request_timeout_in_ms = LOWEST_ACCEPTED_TIMEOUT;
            logger.warn("[CTEST][SET-PARAM] " + "write_request_timeout_in_ms" + getStackTrace()); //CTEST
        }

        if(conf.cas_contention_timeout_in_ms < LOWEST_ACCEPTED_TIMEOUT)
        {
           logInfo("cas_contention_timeout_in_ms", conf.cas_contention_timeout_in_ms, LOWEST_ACCEPTED_TIMEOUT);
           conf.cas_contention_timeout_in_ms = LOWEST_ACCEPTED_TIMEOUT;
            logger.warn("[CTEST][SET-PARAM] " + "cas_contention_timeout_in_ms" + getStackTrace()); //CTEST
        }

        if(conf.counter_write_request_timeout_in_ms < LOWEST_ACCEPTED_TIMEOUT)
        {
           logInfo("counter_write_request_timeout_in_ms", conf.counter_write_request_timeout_in_ms, LOWEST_ACCEPTED_TIMEOUT);
           conf.counter_write_request_timeout_in_ms = LOWEST_ACCEPTED_TIMEOUT;
            logger.warn("[CTEST][SET-PARAM] " + "counter_write_request_timeout_in_ms" + getStackTrace()); //CTEST
        }

        if(conf.truncate_request_timeout_in_ms < LOWEST_ACCEPTED_TIMEOUT)
        {
           logInfo("truncate_request_timeout_in_ms", conf.truncate_request_timeout_in_ms, LOWEST_ACCEPTED_TIMEOUT);
           conf.truncate_request_timeout_in_ms = LOWEST_ACCEPTED_TIMEOUT;
            logger.warn("[CTEST][SET-PARAM] " + "truncate_request_timeout_in_ms" + getStackTrace()); //CTEST
        }
    }

    private static void logInfo(String property, long actualValue, long lowestAcceptedValue)
    {
        logger.info("found {}::{} less than lowest acceptable value {}, continuing with {}", property, actualValue, lowestAcceptedValue, lowestAcceptedValue);
    }

    public static void applyTokensConfig()
    {
        applyTokensConfig(conf);
    }

    static void applyTokensConfig(Config conf)
    {
        logger.warn("[CTEST][GET-PARAM] " + "initial_token" ); //CTEST
        if (conf.initial_token != null)
        {
            Collection<String> tokens = tokensFromString(conf.initial_token);
            if (conf.num_tokens == null)
            {
                if (tokens.size() == 1) {
                    conf.num_tokens = 1;
                    logger.warn("[CTEST][SET-PARAM] " + "num_tokens" + getStackTrace()); //CTEST
                }
                else
                    throw new ConfigurationException("initial_token was set but num_tokens is not!", false);
            }

            if (tokens.size() != conf.num_tokens)
            {
                throw new ConfigurationException(String.format("The number of initial tokens (by initial_token) specified (%s) is different from num_tokens value (%s)",
                                                               tokens.size(),
                                                               conf.num_tokens),
                                                 false);
            }

            for (String token : tokens)
                partitioner.getTokenFactory().validate(token);
        }
        else if (conf.num_tokens == null)
        {
            conf.num_tokens = 1;
            logger.warn("[CTEST][SET-PARAM] " + "num_tokens" + getStackTrace()); //CTEST
        }
    }

    // definitely not safe for tools + clients - implicitly instantiates StorageService
    public static void applySnitch()
    {
        /* end point snitch */
        if (conf.endpoint_snitch == null)
        {
            throw new ConfigurationException("Missing endpoint_snitch directive", false);
        }
        snitch = createEndpointSnitch(conf.dynamic_snitch, conf.endpoint_snitch);
        EndpointSnitchInfo.create();

        localDC = snitch.getLocalDatacenter();
        localComparator = (replica1, replica2) -> {
            boolean local1 = localDC.equals(snitch.getDatacenter(replica1));
            boolean local2 = localDC.equals(snitch.getDatacenter(replica2));
            if (local1 && !local2)
                return -1;
            if (local2 && !local1)
                return 1;
            return 0;
        };
    }

    // definitely not safe for tools + clients - implicitly instantiates schema
    public static void applyPartitioner()
    {
        applyPartitioner(conf);
    }

    public static void applyPartitioner(Config conf)
    {
        logger.warn("[CTEST][GET-PARAM] " + "partitioner" ); //CTEST
        /* Hashing strategy */
        if (conf.partitioner == null)
        {
            throw new ConfigurationException("Missing directive: partitioner", false);
        }
        String name = conf.partitioner;
        try
        {
            name = System.getProperty(Config.PROPERTY_PREFIX + "partitioner", conf.partitioner);
            partitioner = FBUtilities.newPartitioner(name);
        }
        catch (Exception e)
        {
            throw new ConfigurationException("Invalid partitioner class " + name, e);
        }

        paritionerName = partitioner.getClass().getCanonicalName();
    }

    /**
     * Computes the sum of the 2 specified positive values returning {@code Long.MAX_VALUE} if the sum overflow.
     *
     * @param left the left operand
     * @param right the right operand
     * @return the sum of the 2 specified positive values of {@code Long.MAX_VALUE} if the sum overflow.
     */
    private static long saturatedSum(long left, long right)
    {
        assert left >= 0 && right >= 0;
        long sum = left + right;
        return sum < 0 ? Long.MAX_VALUE : sum;
    }

    private static FileStore guessFileStore(String dir) throws IOException
    {
        Path path = Paths.get(dir);
        while (true)
        {
            try
            {
                return FileUtils.getFileStore(path);
            }
            catch (IOException e)
            {
                if (e instanceof NoSuchFileException)
                {
                    path = path.getParent();
                    if (path == null)
                    {
                        throw new ConfigurationException("Unable to find filesystem for '" + dir + "'.");
                    }
                }
                else
                {
                    throw e;
                }
            }
        }
    }

    private static long getUnallocatedSpace(String directory)
    {
        try
        {
            return guessFileStore(directory).getUnallocatedSpace();
        }
        catch (IOException e)
        {
            logger.debug("Error checking disk space", e);
            throw new ConfigurationException(String.format("Unable to check disk space available to %s. Perhaps the Cassandra user does not have the necessary permissions",
                                                           directory), e);
        }
    }

    public static IEndpointSnitch createEndpointSnitch(boolean dynamic, String snitchClassName) throws ConfigurationException
    {
        if (!snitchClassName.contains("."))
            snitchClassName = "org.apache.cassandra.locator." + snitchClassName;
        IEndpointSnitch snitch = FBUtilities.construct(snitchClassName, "snitch");
        return dynamic ? new DynamicEndpointSnitch(snitch) : snitch;
    }

    public static IAuthenticator getAuthenticator()
    {
        logger.warn("[CTEST][GET-PARAM] " + "authenticator" ); //CTEST
        return authenticator;
    }

    public static void setAuthenticator(IAuthenticator authenticator)
    {
        logger.warn("[CTEST][SET-PARAM] " + "authenticator" + getStackTrace()); //CTEST
        DatabaseDescriptor.authenticator = authenticator;
    }

    public static IAuthorizer getAuthorizer()
    {
        logger.warn("[CTEST][GET-PARAM] " + "authorizer" ); //CTEST
        return authorizer;
    }

    public static void setAuthorizer(IAuthorizer authorizer)
    {
        logger.warn("[CTEST][SET-PARAM] " + "authorizer" + getStackTrace()); //CTEST
        DatabaseDescriptor.authorizer = authorizer;
    }

    public static INetworkAuthorizer getNetworkAuthorizer()
    {
        logger.warn("[CTEST][GET-PARAM] " + "networkAuthorizer" ); //CTEST
        return networkAuthorizer;
    }

    public static void setNetworkAuthorizer(INetworkAuthorizer networkAuthorizer)
    {
        logger.warn("[CTEST][SET-PARAM] " + "networkAuthorizer" + getStackTrace()); //CTEST
        DatabaseDescriptor.networkAuthorizer = networkAuthorizer;
    }

    public static IRoleManager getRoleManager()
    {
        logger.warn("[CTEST][GET-PARAM] " + "roleManager" ); //CTEST
        return roleManager;
    }

    public static void setRoleManager(IRoleManager roleManager)
    {
        logger.warn("[CTEST][SET-PARAM] " + "roleManager" + getStackTrace()); //CTEST
        DatabaseDescriptor.roleManager = roleManager;
    }

    public static int getPermissionsValidity()
    {
        logger.warn("[CTEST][GET-PARAM] " + "permissions_validity_in_ms" ); //CTEST
        return conf.permissions_validity_in_ms;
    }

    public static void setPermissionsValidity(int timeout)
    {
        logger.warn("[CTEST][SET-PARAM] " + "rolemanager" + getStackTrace()); //CTEST
        conf.permissions_validity_in_ms = timeout;
    }

    public static int getPermissionsUpdateInterval()
    {
        logger.warn("[CTEST][GET-PARAM] " + "permissions_update_interval_in_ms" ); //CTEST
        logger.warn("[CTEST][GET-PARAM] " + "permissions_validity_in_ms" ); //CTEST
        return conf.permissions_update_interval_in_ms == -1
             ? conf.permissions_validity_in_ms
             : conf.permissions_update_interval_in_ms;
    }

    public static void setPermissionsUpdateInterval(int updateInterval)
    {
        logger.warn("[CTEST][SET-PARAM] " + "permissions_update_interval_in_ms" + getStackTrace()); //CTEST
        conf.permissions_update_interval_in_ms = updateInterval;
    }

    public static int getPermissionsCacheMaxEntries()
    {
        logger.warn("[CTEST][GET-PARAM] " + "permissions_cache_max_entries" ); //CTEST
        return conf.permissions_cache_max_entries;
    }

    public static int setPermissionsCacheMaxEntries(int maxEntries)
    {
        logger.warn("[CTEST][GET-PARAM] " + "permissions_cache_max_entries" ); //CTEST
        return conf.permissions_cache_max_entries = maxEntries;
    }

    public static int getRolesValidity()
    {
        logger.warn("[CTEST][GET-PARAM] " + "roles_validity_in_ms" ); //CTEST
        return conf.roles_validity_in_ms;
    }

    public static void setRolesValidity(int validity)
    {
        logger.warn("[CTEST][SET-PARAM] " + "roles_validity_in_ms" + getStackTrace()); //CTEST
        conf.roles_validity_in_ms = validity;
    }

    public static int getRolesUpdateInterval()
    {
        logger.warn("[CTEST][GET-PARAM] " + "roles_update_interval_in_ms" ); //CTEST
        logger.warn("[CTEST][GET-PARAM] " + "roles_validity_in_ms" ); //CTEST
        return conf.roles_update_interval_in_ms == -1
             ? conf.roles_validity_in_ms
             : conf.roles_update_interval_in_ms;
    }

    public static void setRolesUpdateInterval(int interval)
    {
        logger.warn("[CTEST][SET-PARAM] " + "roles_update_interval_in_ms" + getStackTrace()); //CTEST
        conf.roles_update_interval_in_ms = interval;
    }

    public static int getRolesCacheMaxEntries()
    {
        logger.warn("[CTEST][GET-PARAM] " + "roles_cache_max_entries" ); //CTEST
        return conf.roles_cache_max_entries;
    }

    public static int setRolesCacheMaxEntries(int maxEntries)
    {
        logger.warn("[CTEST][GET-PARAM] " + "roles_cache_max_entries" ); //CTEST
        return conf.roles_cache_max_entries = maxEntries;
    }

    public static int getCredentialsValidity()
    {
        logger.warn("[CTEST][GET-PARAM] " + "credentials_validity_in_ms" ); //CTEST
        return conf.credentials_validity_in_ms;
    }

    public static void setCredentialsValidity(int timeout)
    {
        logger.warn("[CTEST][SET-PARAM] " + "credentials_validity_in_ms" + getStackTrace()); //CTEST
        conf.credentials_validity_in_ms = timeout;
    }

    public static int getCredentialsUpdateInterval()
    {
        logger.warn("[CTEST][GET-PARAM] " + "credentials_update_interval_in_ms" ); //CTEST
        logger.warn("[CTEST][GET-PARAM] " + "credentials_validity_in_ms" ); //CTEST
        return conf.credentials_update_interval_in_ms == -1
               ? conf.credentials_validity_in_ms
               : conf.credentials_update_interval_in_ms;
    }

    public static void setCredentialsUpdateInterval(int updateInterval)
    {
        logger.warn("[CTEST][SET-PARAM] " + "credentials_update_interval_in_ms" + getStackTrace()); //CTEST
        conf.credentials_update_interval_in_ms = updateInterval;
    }

    public static int getCredentialsCacheMaxEntries()
    {
        logger.warn("[CTEST][GET-PARAM] " + "credentials_cache_max_entries" ); //CTEST
        return conf.credentials_cache_max_entries;
    }

    public static int setCredentialsCacheMaxEntries(int maxEntries)
    {
        logger.warn("[CTEST][GET-PARAM] " + "credentials_cache_max_entries" ); //CTEST
        return conf.credentials_cache_max_entries = maxEntries;
    }

    public static int getMaxValueSize()
    {
        logger.warn("[CTEST][GET-PARAM] " + "max_value_size_in_mb" ); //CTEST
        return conf.max_value_size_in_mb * 1024 * 1024;
    }

    public static void setMaxValueSize(int maxValueSizeInBytes)
    {
        logger.warn("[CTEST][SET-PARAM] " + "max_value_size_in_mb" + getStackTrace()); //CTEST
        conf.max_value_size_in_mb = maxValueSizeInBytes / 1024 / 1024;
    }

    /**
     * Creates all storage-related directories.
     */
    public static void createAllDirectories()
    {
        try
        {
            logger.warn("[CTEST][GET-PARAM] " + "data_file_directories" ); //CTEST
            if (conf.data_file_directories.length == 0)
                throw new ConfigurationException("At least one DataFileDirectory must be specified", false);

            for (String dataFileDirectory : conf.data_file_directories)
                FileUtils.createDirectory(dataFileDirectory);

            logger.warn("[CTEST][GET-PARAM] " + "local_system_data_file_directory" ); //CTEST
            if (conf.local_system_data_file_directory != null)
                FileUtils.createDirectory(conf.local_system_data_file_directory);

            logger.warn("[CTEST][GET-PARAM] " + "commitlog_directory" ); //CTEST
            if (conf.commitlog_directory == null)
                throw new ConfigurationException("commitlog_directory must be specified", false);
            FileUtils.createDirectory(conf.commitlog_directory);

            logger.warn("[CTEST][GET-PARAM] " + "hints_directory" ); //CTEST
            if (conf.hints_directory == null)
                throw new ConfigurationException("hints_directory must be specified", false);
            FileUtils.createDirectory(conf.hints_directory);

            logger.warn("[CTEST][GET-PARAM] " + "saved_caches_directory" ); //CTEST
            if (conf.saved_caches_directory == null)
                throw new ConfigurationException("saved_caches_directory must be specified", false);
            FileUtils.createDirectory(conf.saved_caches_directory);

            logger.warn("[CTEST][GET-PARAM] " + "cdc_enabled" ); //CTEST
            if (conf.cdc_enabled)
            {
                logger.warn("[CTEST][GET-PARAM] " + "cdc_raw_directory" ); //CTEST
                if (conf.cdc_raw_directory == null)
                    throw new ConfigurationException("cdc_raw_directory must be specified", false);
                FileUtils.createDirectory(conf.cdc_raw_directory);
            }
        }
        catch (ConfigurationException e)
        {
            throw new IllegalArgumentException("Bad configuration; unable to start server: "+e.getMessage());
        }
        catch (FSWriteError e)
        {
            throw new IllegalStateException(e.getCause().getMessage() + "; unable to start server");
        }
    }

    public static IPartitioner getPartitioner()
    {
        return partitioner;
    }

    public static String getPartitionerName()
    {
        return paritionerName;
    }

    /* For tests ONLY, don't use otherwise or all hell will break loose. Tests should restore value at the end. */
    public static IPartitioner setPartitionerUnsafe(IPartitioner newPartitioner)
    {
        IPartitioner old = partitioner;
        partitioner = newPartitioner;
        return old;
    }

    public static IEndpointSnitch getEndpointSnitch()
    {
        return snitch;
    }
    public static void setEndpointSnitch(IEndpointSnitch eps)
    {
        snitch = eps;
    }

    public static int getColumnIndexSize()
    {
        logger.warn("[CTEST][GET-PARAM] " + "column_index_size_in_kb" ); //CTEST
        return (int) ByteUnit.KIBI_BYTES.toBytes(conf.column_index_size_in_kb);
    }

    public static int getColumnIndexSizeInKB()
    {
        logger.warn("[CTEST][GET-PARAM] " + "column_index_size_in_kb" ); //CTEST
        return conf.column_index_size_in_kb;
    }

    @VisibleForTesting
    public static void setColumnIndexSize(int val)
    {
        checkValidForByteConversion(val, "column_index_size_in_kb", ByteUnit.KIBI_BYTES);
        conf.column_index_size_in_kb = val;
        logger.warn("[CTEST][SET-PARAM] " + "column_index_size_in_kb" + getStackTrace()); //CTEST
    }

    public static int getColumnIndexCacheSize()
    {
        logger.warn("[CTEST][GET-PARAM] " + "column_index_cache_size_in_kb" ); //CTEST
        return (int) ByteUnit.KIBI_BYTES.toBytes(conf.column_index_cache_size_in_kb);
    }

    public static int getColumnIndexCacheSizeInKB()
    {
        logger.warn("[CTEST][GET-PARAM] " + "column_index_cache_size_in_kb" ); //CTEST
        return conf.column_index_cache_size_in_kb;
    }

    public static void setColumnIndexCacheSize(int val)
    {
        checkValidForByteConversion(val, "column_index_cache_size_in_kb", ByteUnit.KIBI_BYTES);
        conf.column_index_cache_size_in_kb = val;
        logger.warn("[CTEST][SET-PARAM] " + "column_index_cache_size_in_kb" + getStackTrace()); //CTEST
    }

    public static int getBatchSizeWarnThreshold()
    {
        logger.warn("[CTEST][GET-PARAM] " + "batch_size_warn_threshold_in_kb" ); //CTEST
        return (int) ByteUnit.KIBI_BYTES.toBytes(conf.batch_size_warn_threshold_in_kb);
    }

    public static int getBatchSizeWarnThresholdInKB()
    {
        logger.warn("[CTEST][GET-PARAM] " + "batch_size_warn_threshold_in_kb" ); //CTEST
        return conf.batch_size_warn_threshold_in_kb;
    }

    public static long getBatchSizeFailThreshold()
    {
        logger.warn("[CTEST][GET-PARAM] " + "batch_size_fail_threshold_in_kb" ); //CTEST
        return ByteUnit.KIBI_BYTES.toBytes(conf.batch_size_fail_threshold_in_kb);
    }

    public static int getBatchSizeFailThresholdInKB()
    {
        logger.warn("[CTEST][GET-PARAM] " + "batch_size_fail_threshold_in_kb" ); //CTEST
        return conf.batch_size_fail_threshold_in_kb;
    }

    public static int getUnloggedBatchAcrossPartitionsWarnThreshold()
    {
        logger.warn("[CTEST][GET-PARAM] " + "unlogged_batch_across_partitions_warn_threshold" ); //CTEST
        return conf.unlogged_batch_across_partitions_warn_threshold;
    }

    public static void setBatchSizeWarnThresholdInKB(int threshold)
    {
        checkValidForByteConversion(threshold, "batch_size_warn_threshold_in_kb", ByteUnit.KIBI_BYTES);
        conf.batch_size_warn_threshold_in_kb = threshold;
        logger.warn("[CTEST][SET-PARAM] " + "batch_size_warn_threshold_in_kb" + getStackTrace()); //CTEST
    }

    public static void setBatchSizeFailThresholdInKB(int threshold)
    {
        conf.batch_size_fail_threshold_in_kb = threshold;
        logger.warn("[CTEST][SET-PARAM] " + "batch_size_fail_threshold_in_kb" + getStackTrace()); //CTEST
    }

    public static Collection<String> getInitialTokens()
    {
        logger.warn("[CTEST][GET-PARAM] " + "initial_token" ); //CTEST
        return tokensFromString(System.getProperty(Config.PROPERTY_PREFIX + "initial_token", conf.initial_token));
    }

    public static String getAllocateTokensForKeyspace()
    {
        logger.warn("[CTEST][GET-PARAM] " + "allocate_tokens_for_keyspace" ); //CTEST
        return System.getProperty(Config.PROPERTY_PREFIX + "allocate_tokens_for_keyspace", conf.allocate_tokens_for_keyspace);
    }

    public static Integer getAllocateTokensForLocalRf()
    {
        logger.warn("[CTEST][GET-PARAM] " + "allocate_tokens_for_local_replication_factor" ); //CTEST
        return conf.allocate_tokens_for_local_replication_factor;
    }

    public static Collection<String> tokensFromString(String tokenString)
    {
        List<String> tokens = new ArrayList<>();
        if (tokenString != null)
            for (String token : StringUtils.split(tokenString, ','))
                tokens.add(token.trim());
        return tokens;
    }

    public static int getNumTokens()
    {
        logger.warn("[CTEST][GET-PARAM] " + "num_tokens" ); //CTEST
        return conf.num_tokens;
    }

    public static InetAddressAndPort getReplaceAddress()
    {
        try
        {
            if (System.getProperty(Config.PROPERTY_PREFIX + "replace_address", null) != null)
                return InetAddressAndPort.getByName(System.getProperty(Config.PROPERTY_PREFIX + "replace_address", null));
            else if (System.getProperty(Config.PROPERTY_PREFIX + "replace_address_first_boot", null) != null)
                return InetAddressAndPort.getByName(System.getProperty(Config.PROPERTY_PREFIX + "replace_address_first_boot", null));
            return null;
        }
        catch (UnknownHostException e)
        {
            throw new RuntimeException("Replacement host name could not be resolved or scope_id was specified for a global IPv6 address", e);
        }
    }

    public static Collection<String> getReplaceTokens()
    {
        return tokensFromString(System.getProperty(Config.PROPERTY_PREFIX + "replace_token", null));
    }

    public static UUID getReplaceNode()
    {
        try
        {
            return UUID.fromString(System.getProperty(Config.PROPERTY_PREFIX + "replace_node", null));
        } catch (NullPointerException e)
        {
            return null;
        }
    }

    public static String getClusterName()
    {
        logger.warn("[CTEST][GET-PARAM] " + "cluster_name" ); //CTEST
        return conf.cluster_name;
    }

    public static int getStoragePort()
    {
        logger.warn("[CTEST][GET-PARAM] " + "storage_port" ); //CTEST
        return Integer.parseInt(System.getProperty(Config.PROPERTY_PREFIX + "storage_port", Integer.toString(conf.storage_port)));
    }

    public static int getSSLStoragePort()
    {
        return Integer.parseInt(System.getProperty(Config.PROPERTY_PREFIX + "ssl_storage_port", Integer.toString(conf.ssl_storage_port)));
    }

    public static long nativeTransportIdleTimeout()
    {
        logger.warn("[CTEST][GET-PARAM] " + "native_transport_idle_timeout_in_ms" ); //CTEST
        return conf.native_transport_idle_timeout_in_ms;
    }

    public static void setNativeTransportIdleTimeout(long nativeTransportTimeout)
    {
        conf.native_transport_idle_timeout_in_ms = nativeTransportTimeout;
        logger.warn("[CTEST][SET-PARAM] " + "native_transport_idle_timeout_in_ms" + getStackTrace()); //CTEST
    }

    public static long getRpcTimeout(TimeUnit unit)
    {
        logger.warn("[CTEST][GET-PARAM] " + "request_timeout_in_ms" ); //CTEST
        return unit.convert(conf.request_timeout_in_ms, MILLISECONDS);
    }

    public static void setRpcTimeout(long timeOutInMillis)
    {
        conf.request_timeout_in_ms = timeOutInMillis;
        logger.warn("[CTEST][SET-PARAM] " + "request_timeout_in_ms" + getStackTrace()); //CTEST
    }

    public static long getReadRpcTimeout(TimeUnit unit)
    {
        logger.warn("[CTEST][GET-PARAM] " + "read_request_timeout_in_ms" ); //CTEST
        return unit.convert(conf.read_request_timeout_in_ms, MILLISECONDS);
    }

    public static void setReadRpcTimeout(long timeOutInMillis)
    {
        conf.read_request_timeout_in_ms = timeOutInMillis;
        logger.warn("[CTEST][SET-PARAM] " + "read_request_timeout_in_ms" + getStackTrace()); //CTEST
    }

    public static long getRangeRpcTimeout(TimeUnit unit)
    {
        logger.warn("[CTEST][GET-PARAM] " + "range_request_timeout_in_ms" ); //CTEST
        return unit.convert(conf.range_request_timeout_in_ms, MILLISECONDS);
    }

    public static void setRangeRpcTimeout(long timeOutInMillis)
    {
        conf.range_request_timeout_in_ms = timeOutInMillis;
        logger.warn("[CTEST][SET-PARAM] " + "range_request_timeout_in_ms" + getStackTrace()); //CTEST
    }

    public static long getWriteRpcTimeout(TimeUnit unit)
    {
        logger.warn("[CTEST][GET-PARAM] " + "write_request_timeout_in_ms" ); //CTEST
        return unit.convert(conf.write_request_timeout_in_ms, MILLISECONDS);
    }

    public static void setWriteRpcTimeout(long timeOutInMillis)
    {
        conf.write_request_timeout_in_ms = timeOutInMillis;
        logger.warn("[CTEST][SET-PARAM] " + "write_request_timeout_in_ms" + getStackTrace()); //CTEST
    }

    public static long getCounterWriteRpcTimeout(TimeUnit unit)
    {
        logger.warn("[CTEST][GET-PARAM] " + "counter_write_request_timeout_in_ms" ); //CTEST
        return unit.convert(conf.counter_write_request_timeout_in_ms, MILLISECONDS);
    }

    public static void setCounterWriteRpcTimeout(long timeOutInMillis)
    {
        conf.counter_write_request_timeout_in_ms = timeOutInMillis;
        logger.warn("[CTEST][SET-PARAM] " + "counter_write_request_timeout_in_ms" + getStackTrace()); //CTEST
    }

    public static long getCasContentionTimeout(TimeUnit unit)
    {
        logger.warn("[CTEST][GET-PARAM] " + "cas_contention_timeout_in_ms" ); //CTEST
        return unit.convert(conf.cas_contention_timeout_in_ms, MILLISECONDS);
    }

    public static void setCasContentionTimeout(long timeOutInMillis)
    {
        conf.cas_contention_timeout_in_ms = timeOutInMillis;
        logger.warn("[CTEST][SET-PARAM] " + "cas_contention_timeout_in_ms" + getStackTrace()); //CTEST
    }

    public static long getTruncateRpcTimeout(TimeUnit unit)
    {
        logger.warn("[CTEST][GET-PARAM] " + "truncate_request_timeout_in_ms" ); //CTEST
        return unit.convert(conf.truncate_request_timeout_in_ms, MILLISECONDS);
    }

    public static void setTruncateRpcTimeout(long timeOutInMillis)
    {
        conf.truncate_request_timeout_in_ms = timeOutInMillis;
        logger.warn("[CTEST][SET-PARAM] " + "truncate_request_timeout_in_ms" + getStackTrace()); //CTEST
    }

    public static boolean hasCrossNodeTimeout()
    {
        logger.warn("[CTEST][GET-PARAM] " + "cross_node_timeout" ); //CTEST
        return conf.cross_node_timeout;
    }

    public static void setCrossNodeTimeout(boolean crossNodeTimeout)
    {
        conf.cross_node_timeout = crossNodeTimeout;
        logger.warn("[CTEST][SET-PARAM] " + "cross_node_timeout" + getStackTrace()); //CTEST
    }

    public static long getSlowQueryTimeout(TimeUnit units)
    {
        logger.warn("[CTEST][GET-PARAM] " + "slow_query_log_timeout_in_ms" ); //CTEST
        return units.convert(conf.slow_query_log_timeout_in_ms, MILLISECONDS);
    }

    /**
     * @return the minimum configured {read, write, range, truncate, misc} timeout
     */
    public static long getMinRpcTimeout(TimeUnit unit)
    {
        return Longs.min(getRpcTimeout(unit),
                         getReadRpcTimeout(unit),
                         getRangeRpcTimeout(unit),
                         getWriteRpcTimeout(unit),
                         getCounterWriteRpcTimeout(unit),
                         getTruncateRpcTimeout(unit));
    }

    public static long getPingTimeout(TimeUnit unit)
    {
        return unit.convert(getBlockForPeersTimeoutInSeconds(), TimeUnit.SECONDS);
    }

    public static long getRepairRpcTimeout(TimeUnit unit)
    {
        logger.warn("[CTEST][GET-PARAM] " + "repair_request_timeout_in_ms" ); //CTEST
        return unit.convert(conf.repair_request_timeout_in_ms, MILLISECONDS);
    }

    public static void setRepairRpcTimeout(long time, TimeUnit unit)
    {
        conf.repair_request_timeout_in_ms = MILLISECONDS.convert(time, unit);
        logger.warn("[CTEST][SET-PARAM] " + "repair_request_timeout_in_ms" + getStackTrace()); //CTEST
    }

    public static double getPhiConvictThreshold()
    {
        logger.warn("[CTEST][GET-PARAM] " + "phi_convict_threshold" ); //CTEST
        return conf.phi_convict_threshold;
    }

    public static void setPhiConvictThreshold(double phiConvictThreshold)
    {
        conf.phi_convict_threshold = phiConvictThreshold;
        logger.warn("[CTEST][SET-PARAM] " + "phi_convict_threshold" + getStackTrace()); //CTEST
    }

    public static int getConcurrentReaders()
    {
        logger.warn("[CTEST][GET-PARAM] " + "concurrent_reads" ); //CTEST
        return conf.concurrent_reads;
    }

    public static void setConcurrentReaders(int concurrent_reads)
    {
        if (concurrent_reads < 0)
        {
            throw new IllegalArgumentException("Concurrent reads must be non-negative");
        }
        conf.concurrent_reads = concurrent_reads;
        logger.warn("[CTEST][SET-PARAM] " + "concurrent_reads" + getStackTrace()); //CTEST
    }

    public static int getConcurrentWriters()
    {
        logger.warn("[CTEST][GET-PARAM] " + "concurrent_writes" ); //CTEST
        return conf.concurrent_writes;
    }

    public static void setConcurrentWriters(int concurrent_writers)
    {
        if (concurrent_writers < 0)
        {
            throw new IllegalArgumentException("Concurrent reads must be non-negative");
        }
        conf.concurrent_writes = concurrent_writers;
        logger.warn("[CTEST][SET-PARAM] " + "concurrent_writes" + getStackTrace()); //CTEST
    }

    public static int getConcurrentCounterWriters()
    {
        logger.warn("[CTEST][GET-PARAM] " + "concurrent_counter_writes" ); //CTEST
        return conf.concurrent_counter_writes;
    }

    public static void setConcurrentCounterWriters(int concurrent_counter_writes)
    {
        if (concurrent_counter_writes < 0)
        {
            throw new IllegalArgumentException("Concurrent reads must be non-negative");
        }
        conf.concurrent_counter_writes = concurrent_counter_writes;
        logger.warn("[CTEST][SET-PARAM] " + "concurrent_counter_writes" + getStackTrace()); //CTEST
    }

    public static int getConcurrentViewWriters()
    {
        logger.warn("[CTEST][GET-PARAM] " + "concurrent_materialized_view_writes" ); //CTEST
        return conf.concurrent_materialized_view_writes;
    }

    public static void setConcurrentViewWriters(int concurrent_materialized_view_writes)
    {
        if (concurrent_materialized_view_writes < 0)
        {
            throw new IllegalArgumentException("Concurrent reads must be non-negative");
        }
        conf.concurrent_materialized_view_writes = concurrent_materialized_view_writes;
        logger.warn("[CTEST][SET-PARAM] " + "concurrent_materialized_view_writes" + getStackTrace()); //CTEST
    }

    public static int getFlushWriters()
    {
        logger.warn("[CTEST][GET-PARAM] " + "memtable_flush_writers" ); //CTEST
        return conf.memtable_flush_writers;
    }

    public static int getConcurrentCompactors()
    {
        logger.warn("[CTEST][GET-PARAM] " + "concurrent_compactors" ); //CTEST
        return conf.concurrent_compactors;
    }

    public static void setConcurrentCompactors(int value)
    {
        conf.concurrent_compactors = value;
        logger.warn("[CTEST][SET-PARAM] " + "concurrent_compactors" + getStackTrace()); //CTEST
    }

    public static int getCompactionThroughputMbPerSec()
    {
        logger.warn("[CTEST][GET-PARAM] " + "compaction_throughput_mb_per_sec" ); //CTEST
        return conf.compaction_throughput_mb_per_sec;
    }

    public static void setCompactionThroughputMbPerSec(int value)
    {
        conf.compaction_throughput_mb_per_sec = value;
        logger.warn("[CTEST][SET-PARAM] " + "compaction_throughput_mb_per_sec" + getStackTrace()); //CTEST
    }

    public static long getCompactionLargePartitionWarningThreshold() {
        logger.warn("[CTEST][GET-PARAM] " + "compaction_large_partition_warning_threshold_mb" ); //CTEST
        return ByteUnit.MEBI_BYTES.toBytes(conf.compaction_large_partition_warning_threshold_mb);
    }

    public static int getConcurrentValidations()
    {
        logger.warn("[CTEST][GET-PARAM] " + "concurrent_validations" ); //CTEST
        return conf.concurrent_validations;
    }

    public static void setConcurrentValidations(int value)
    {
        value = value > 0 ? value : Integer.MAX_VALUE;
        conf.concurrent_validations = value;
        logger.warn("[CTEST][SET-PARAM] " + "concurrent_validations" + getStackTrace()); //CTEST
    }

    public static int getConcurrentViewBuilders()
    {
        logger.warn("[CTEST][GET-PARAM] " + "concurrent_materialized_view_builders" ); //CTEST
        return conf.concurrent_materialized_view_builders;
    }

    public static void setConcurrentViewBuilders(int value)
    {
        conf.concurrent_materialized_view_builders = value;
        logger.warn("[CTEST][SET-PARAM] " + "concurrent_materialized_view_builders" + getStackTrace()); //CTEST
    }

    public static long getMinFreeSpacePerDriveInBytes()
    {
        logger.warn("[CTEST][GET-PARAM] " + "min_free_space_per_drive_in_mb" ); //CTEST
        return ByteUnit.MEBI_BYTES.toBytes(conf.min_free_space_per_drive_in_mb);
    }

    public static boolean getDisableSTCSInL0()
    {
        return disableSTCSInL0;
    }

    public static void setDisableSTCSInL0(boolean disabled)
    {
        disableSTCSInL0 = disabled;
    }

    public static int getStreamThroughputOutboundMegabitsPerSec()
    {
        logger.warn("[CTEST][GET-PARAM] " + "stream_throughput_outbound_megabits_per_sec" ); //CTEST
        return conf.stream_throughput_outbound_megabits_per_sec;
    }

    public static void setStreamThroughputOutboundMegabitsPerSec(int value)
    {
        conf.stream_throughput_outbound_megabits_per_sec = value;
        logger.warn("[CTEST][SET-PARAM] " + "stream_throughput_outbound_megabits_per_sec" + getStackTrace()); //CTEST
    }

    public static int getInterDCStreamThroughputOutboundMegabitsPerSec()
    {
        logger.warn("[CTEST][GET-PARAM] " + "inter_dc_stream_throughput_outbound_megabits_per_sec" ); //CTEST
        return conf.inter_dc_stream_throughput_outbound_megabits_per_sec;
    }

    public static void setInterDCStreamThroughputOutboundMegabitsPerSec(int value)
    {
        conf.inter_dc_stream_throughput_outbound_megabits_per_sec = value;
        logger.warn("[CTEST][SET-PARAM] " + "inter_dc_stream_throughput_outbound_megabits_per_sec" + getStackTrace()); //CTEST
    }

    /**
     * Checks if the local system data must be stored in a specific location which supports redundancy.
     *
     * @return {@code true} if the local system keyspaces data must be stored in a different location,
     * {@code false} otherwise.
     */
    public static boolean useSpecificLocationForLocalSystemData()
    {
        logger.warn("[CTEST][GET-PARAM] " + "local_system_data_file_directory" ); //CTEST
        return conf.local_system_data_file_directory != null;
    }

    /**
     * Returns the locations where the local system keyspaces data should be stored.
     *
     * <p>If the {@code local_system_data_file_directory} was unspecified, the local system keyspaces data should be stored
     * in the first data directory. This approach guarantees that the server can tolerate the lost of all the disks but the first one.</p>
     *
     * @return the locations where should be stored the local system keyspaces data
     */
    public static String[] getLocalSystemKeyspacesDataFileLocations()
    {
        if (useSpecificLocationForLocalSystemData()) {
            logger.warn("[CTEST][GET-PARAM] " + "local_system_data_file_directory" ); //CTEST
            return new String[] {conf.local_system_data_file_directory};
        }
        logger.warn("[CTEST][GET-PARAM] " + "local_system_data_file_directory" ); //CTEST
        return conf.data_file_directories.length == 0  ? conf.data_file_directories
                                                       : new String[] {conf.data_file_directories[0]};
    }

    /**
     * Returns the locations where the non local system keyspaces data should be stored.
     *
     * @return the locations where the non local system keyspaces data should be stored.
     */
    public static String[] getNonLocalSystemKeyspacesDataFileLocations()
    {
        logger.warn("[CTEST][GET-PARAM] " + "data_file_directories" ); //CTEST
        return conf.data_file_directories;
    }

    /**
     * Returns the list of all the directories where the data files can be stored (for local system and non local system keyspaces).
     *
     * @return the list of all the directories where the data files can be stored.
     */
    public static String[] getAllDataFileLocations()
    {
        logger.warn("[CTEST][GET-PARAM] " + "local_system_data_file_directory" ); //CTEST
        if (conf.local_system_data_file_directory == null) {
            logger.warn("[CTEST][GET-PARAM] " + "data_file_directories" ); //CTEST
            return conf.data_file_directories;
        }
        logger.warn("[CTEST][GET-PARAM] " + "data_file_directories" ); //CTEST
        return ArrayUtils.addFirst(conf.data_file_directories, conf.local_system_data_file_directory);
    }

    public static String getCommitLogLocation()
    {
        logger.warn("[CTEST][GET-PARAM] " + "commitlog_directory" ); //CTEST
        return conf.commitlog_directory;
    }

    @VisibleForTesting
    public static void setCommitLogLocation(String value)
    {
        conf.commitlog_directory = value;
        logger.warn("[CTEST][SET-PARAM] " + "commitlog_directory" + getStackTrace()); //CTEST
    }

    public static ParameterizedClass getCommitLogCompression()
    {
        logger.warn("[CTEST][GET-PARAM] " + "commitlog_compression" ); //CTEST
        return conf.commitlog_compression;
    }

    public static void setCommitLogCompression(ParameterizedClass compressor)
    {
        conf.commitlog_compression = compressor;
        logger.warn("[CTEST][SET-PARAM] " + "commitlog_compression" + getStackTrace()); //CTEST
    }

    public static Config.FlushCompression getFlushCompression()
    {
        logger.warn("[CTEST][GET-PARAM] " + "flush_compression" ); //CTEST
        return conf.flush_compression;
    }

    public static void setFlushCompression(Config.FlushCompression compression)
    {
        conf.flush_compression = compression;
        logger.warn("[CTEST][SET-PARAM] " + "flush_compression" + getStackTrace()); //CTEST
    }

   /**
    * Maximum number of buffers in the compression pool. The default value is 3, it should not be set lower than that
    * (one segment in compression, one written to, one in reserve); delays in compression may cause the log to use
    * more, depending on how soon the sync policy stops all writing threads.
    */
    public static int getCommitLogMaxCompressionBuffersInPool()
    {
        logger.warn("[CTEST][GET-PARAM] " + "commitlog_max_compression_buffers_in_pool" ); //CTEST
        return conf.commitlog_max_compression_buffers_in_pool;
    }

    public static void setCommitLogMaxCompressionBuffersPerPool(int buffers)
    {
        conf.commitlog_max_compression_buffers_in_pool = buffers;
        logger.warn("[CTEST][SET-PARAM] " + "commitlog_max_compression_buffers_in_pool" + getStackTrace()); //CTEST
    }

    public static int getMaxMutationSize()
    {
        logger.warn("[CTEST][GET-PARAM] " + "max_mutation_size_in_kb" ); //CTEST
        return (int) ByteUnit.KIBI_BYTES.toBytes(conf.max_mutation_size_in_kb);
    }

    public static int getTombstoneWarnThreshold()
    {
        logger.warn("[CTEST][GET-PARAM] " + "tombstone_warn_threshold" ); //CTEST
        return conf.tombstone_warn_threshold;
    }

    public static void setTombstoneWarnThreshold(int threshold)
    {
        conf.tombstone_warn_threshold = threshold;
        logger.warn("[CTEST][SET-PARAM] " + "tombstone_warn_threshold" + getStackTrace()); //CTEST
    }

    public static int getTombstoneFailureThreshold()
    {
        logger.warn("[CTEST][GET-PARAM] " + "tombstone_failure_threshold" ); //CTEST
        return conf.tombstone_failure_threshold;
    }

    public static void setTombstoneFailureThreshold(int threshold)
    {
        conf.tombstone_failure_threshold = threshold;
        logger.warn("[CTEST][SET-PARAM] " + "tombstone_failure_threshold" + getStackTrace()); //CTEST
    }

    public static int getCachedReplicaRowsWarnThreshold()
    {
        logger.warn("[CTEST][GET-PARAM] " + "replica_filtering_protection.cached_rows_warn_threshold" ); //CTEST
        return conf.replica_filtering_protection.cached_rows_warn_threshold;
    }

    public static void setCachedReplicaRowsWarnThreshold(int threshold)
    {
        conf.replica_filtering_protection.cached_rows_warn_threshold = threshold;
        logger.warn("[CTEST][SET-PARAM] " + "replica_filtering_protection.cached_rows_warn_threshold" + getStackTrace()); //CTEST
    }

    public static int getCachedReplicaRowsFailThreshold()
    {
        logger.warn("[CTEST][GET-PARAM] " + "replica_filtering_protection.cached_rows_fail_threshold" ); //CTEST
        return conf.replica_filtering_protection.cached_rows_fail_threshold;
    }

    public static void setCachedReplicaRowsFailThreshold(int threshold)
    {
        conf.replica_filtering_protection.cached_rows_fail_threshold = threshold;
        logger.warn("[CTEST][SET-PARAM] " + "replica_filtering_protection.cached_rows_fail_threshold" + getStackTrace()); //CTEST
    }

    /**
     * size of commitlog segments to allocate
     */
    public static int getCommitLogSegmentSize()
    {
        logger.warn("[CTEST][GET-PARAM] " + "commitlog_segment_size_in_mb" ); //CTEST
        return (int) ByteUnit.MEBI_BYTES.toBytes(conf.commitlog_segment_size_in_mb);
    }

    public static void setCommitLogSegmentSize(int sizeMegabytes)
    {
        conf.commitlog_segment_size_in_mb = sizeMegabytes;
        logger.warn("[CTEST][SET-PARAM] " + "commitlog_segment_size_in_mb" + getStackTrace()); //CTEST
    }

    public static String getSavedCachesLocation()
    {
        logger.warn("[CTEST][GET-PARAM] " + "saved_caches_directory" ); //CTEST
        return conf.saved_caches_directory;
    }

    public static Set<InetAddressAndPort> getSeeds()
    {
        return ImmutableSet.<InetAddressAndPort>builder().addAll(seedProvider.getSeeds()).build();
    }

    public static SeedProvider getSeedProvider()
    {
        return seedProvider;
    }

    public static void setSeedProvider(SeedProvider newSeedProvider)
    {
        seedProvider = newSeedProvider;
    }

    public static InetAddress getListenAddress()
    {
        return listenAddress;
    }

    public static void setListenAddress(InetAddress newlistenAddress)
    {
        listenAddress = newlistenAddress;
    }

    public static InetAddress getBroadcastAddress()
    {
        return broadcastAddress;
    }

    public static boolean shouldListenOnBroadcastAddress()
    {
        logger.warn("[CTEST][GET-PARAM] " + "listen_on_broadcast_address" ); //CTEST
        return conf.listen_on_broadcast_address;
    }

    public static void setShouldListenOnBroadcastAddress(boolean shouldListenOnBroadcastAddress)
    {
        conf.listen_on_broadcast_address = shouldListenOnBroadcastAddress;
        logger.warn("[CTEST][SET-PARAM] " + "listen_on_broadcast_address" + getStackTrace()); //CTEST
    }

    public static void setListenOnBroadcastAddress(boolean listen_on_broadcast_address)
    {
        conf.listen_on_broadcast_address = listen_on_broadcast_address;
        logger.warn("[CTEST][SET-PARAM] " + "listen_on_broadcast_address" + getStackTrace()); //CTEST
    }

    public static IInternodeAuthenticator getInternodeAuthenticator()
    {
        return internodeAuthenticator;
    }

    public static void setInternodeAuthenticator(IInternodeAuthenticator internodeAuthenticator)
    {
        Preconditions.checkNotNull(internodeAuthenticator);
        DatabaseDescriptor.internodeAuthenticator = internodeAuthenticator;
    }

    public static void setBroadcastAddress(InetAddress broadcastAdd)
    {
        broadcastAddress = broadcastAdd;
    }

    /**
     * This is the address used to bind for the native protocol to communicate with clients. Most usages in the code
     * refer to it as native address although some places still call it RPC address. It's not thrift RPC anymore
     * so native is more appropriate. The address alone is not enough to uniquely identify this instance because
     * multiple instances might use the same interface with different ports.
     */
    public static InetAddress getRpcAddress()
    {
        return rpcAddress;
    }

    public static void setBroadcastRpcAddress(InetAddress broadcastRPCAddr)
    {
        broadcastRpcAddress = broadcastRPCAddr;
    }

    /**
     * This is the address used to reach this instance for the native protocol to communicate with clients. Most usages in the code
     * refer to it as native address although some places still call it RPC address. It's not thrift RPC anymore
     * so native is more appropriate. The address alone is not enough to uniquely identify this instance because
     * multiple instances might use the same interface with different ports.
     *
     * May be null, please use {@link FBUtilities#getBroadcastNativeAddressAndPort()} instead.
     */
    public static InetAddress getBroadcastRpcAddress()
    {
        return broadcastRpcAddress;
    }

    public static boolean getRpcKeepAlive()
    {
        logger.warn("[CTEST][GET-PARAM] " + "rpc_keepalive" ); //CTEST
        return conf.rpc_keepalive;
    }

    public static int getInternodeSocketSendBufferSizeInBytes()
    {
        logger.warn("[CTEST][GET-PARAM] " + "internode_socket_send_buffer_size_in_bytes" ); //CTEST
        return conf.internode_socket_send_buffer_size_in_bytes;
    }

    public static int getInternodeSocketReceiveBufferSizeInBytes()
    {
        logger.warn("[CTEST][GET-PARAM] " + "internode_socket_receive_buffer_size_in_bytes" ); //CTEST
        return conf.internode_socket_receive_buffer_size_in_bytes;
    }

    public static int getInternodeApplicationSendQueueCapacityInBytes()
    {
        logger.warn("[CTEST][GET-PARAM] " + "internode_application_send_queue_capacity_in_bytes" ); //CTEST
        return conf.internode_application_send_queue_capacity_in_bytes;
    }

    public static int getInternodeApplicationSendQueueReserveEndpointCapacityInBytes()
    {
        logger.warn("[CTEST][GET-PARAM] " + "internode_application_send_queue_reserve_endpoint_capacity_in_bytes" ); //CTEST
        return conf.internode_application_send_queue_reserve_endpoint_capacity_in_bytes;
    }

    public static int getInternodeApplicationSendQueueReserveGlobalCapacityInBytes()
    {
        logger.warn("[CTEST][GET-PARAM] " + "internode_application_send_queue_reserve_global_capacity_in_bytes" ); //CTEST
        return conf.internode_application_send_queue_reserve_global_capacity_in_bytes;
    }

    public static int getInternodeApplicationReceiveQueueCapacityInBytes()
    {
        logger.warn("[CTEST][GET-PARAM] " + "internode_application_receive_queue_capacity_in_bytes" ); //CTEST
        return conf.internode_application_receive_queue_capacity_in_bytes;
    }

    public static int getInternodeApplicationReceiveQueueReserveEndpointCapacityInBytes()
    {
        logger.warn("[CTEST][GET-PARAM] " + "internode_application_receive_queue_reserve_endpoint_capacity_in_bytes" ); //CTEST
        return conf.internode_application_receive_queue_reserve_endpoint_capacity_in_bytes;
    }

    public static int getInternodeApplicationReceiveQueueReserveGlobalCapacityInBytes()
    {
        logger.warn("[CTEST][GET-PARAM] " + "internode_application_receive_queue_reserve_global_capacity_in_bytes" ); //CTEST
        return conf.internode_application_receive_queue_reserve_global_capacity_in_bytes;
    }

    public static int getInternodeTcpConnectTimeoutInMS()
    {
        logger.warn("[CTEST][GET-PARAM] " + "internode_tcp_connect_timeout_in_ms" ); //CTEST
        return conf.internode_tcp_connect_timeout_in_ms;
    }

    public static void setInternodeTcpConnectTimeoutInMS(int value)
    {
        conf.internode_tcp_connect_timeout_in_ms = value;
        logger.warn("[CTEST][SET-PARAM] " + "internode_tcp_connect_timeout_in_ms" + getStackTrace()); //CTEST
    }

    public static int getInternodeTcpUserTimeoutInMS()
    {
        logger.warn("[CTEST][GET-PARAM] " + "internode_tcp_user_timeout_in_ms" ); //CTEST
        return conf.internode_tcp_user_timeout_in_ms;
    }

    public static void setInternodeTcpUserTimeoutInMS(int value)
    {
        conf.internode_tcp_user_timeout_in_ms = value;
        logger.warn("[CTEST][SET-PARAM] " + "internode_tcp_user_timeout_in_ms" + getStackTrace()); //CTEST
    }

    public static int getInternodeStreamingTcpUserTimeoutInMS()
    {
        logger.warn("[CTEST][GET-PARAM] " + "internode_streaming_tcp_user_timeout_in_ms" ); //CTEST
        return conf.internode_streaming_tcp_user_timeout_in_ms;
    }

    public static void setInternodeStreamingTcpUserTimeoutInMS(int value)
    {
        conf.internode_streaming_tcp_user_timeout_in_ms = value;
        logger.warn("[CTEST][SET-PARAM] " + "internode_streaming_tcp_user_timeout_in_ms" + getStackTrace()); //CTEST
    }

    public static int getInternodeMaxMessageSizeInBytes()
    {
        logger.warn("[CTEST][GET-PARAM] " + "internode_max_message_size_in_bytes" ); //CTEST
        return conf.internode_max_message_size_in_bytes;
    }

    @VisibleForTesting
    public static void setInternodeMaxMessageSizeInBytes(int value)
    {
        conf.internode_max_message_size_in_bytes = value;
        logger.warn("[CTEST][SET-PARAM] " + "internode_max_message_size_in_bytes" + getStackTrace()); //CTEST
    }

    public static boolean startNativeTransport()
    {
        logger.warn("[CTEST][GET-PARAM] " + "start_native_transport" ); //CTEST
        return conf.start_native_transport;
    }

    /**
     *  This is the port used with RPC address for the native protocol to communicate with clients. Now that thrift RPC
     *  is no longer in use there is no RPC port.
     */
    public static int getNativeTransportPort()
    {
        logger.warn("[CTEST][GET-PARAM] " + "native_transport_port" ); //CTEST
        return Integer.parseInt(System.getProperty(Config.PROPERTY_PREFIX + "native_transport_port", Integer.toString(conf.native_transport_port)));
    }

    @VisibleForTesting
    public static void setNativeTransportPort(int port)
    {
        conf.native_transport_port = port;
        logger.warn("[CTEST][SET-PARAM] " + "native_transport_port" + getStackTrace()); //CTEST
    }

    public static int getNativeTransportPortSSL()
    {
        logger.warn("[CTEST][GET-PARAM] " + "native_transport_port_ssl" ); //CTEST
        return conf.native_transport_port_ssl == null ? getNativeTransportPort() : conf.native_transport_port_ssl;
    }

    @VisibleForTesting
    public static void setNativeTransportPortSSL(Integer port)
    {
        conf.native_transport_port_ssl = port;
        logger.warn("[CTEST][SET-PARAM] " + "native_transport_port_ssl" + getStackTrace()); //CTEST
    }

    public static int getNativeTransportMaxThreads()
    {
        logger.warn("[CTEST][GET-PARAM] " + "native_transport_max_threads" ); //CTEST
        return conf.native_transport_max_threads;
    }

    public static void setNativeTransportMaxThreads(int max_threads)
    {
        conf.native_transport_max_threads = max_threads;
        logger.warn("[CTEST][SET-PARAM] " + "native_transport_max_threads" + getStackTrace()); //CTEST
    }

    public static int getNativeTransportMaxFrameSize()
    {
        logger.warn("[CTEST][GET-PARAM] " + "native_transport_max_frame_size_in_mb" ); //CTEST
        return (int) ByteUnit.MEBI_BYTES.toBytes(conf.native_transport_max_frame_size_in_mb);
    }

    public static long getNativeTransportMaxConcurrentConnections()
    {
        logger.warn("[CTEST][GET-PARAM] " + "native_transport_max_concurrent_connections" ); //CTEST
        return conf.native_transport_max_concurrent_connections;
    }

    public static void setNativeTransportMaxConcurrentConnections(long nativeTransportMaxConcurrentConnections)
    {
        conf.native_transport_max_concurrent_connections = nativeTransportMaxConcurrentConnections;
        logger.warn("[CTEST][SET-PARAM] " + "native_transport_max_concurrent_connections" + getStackTrace()); //CTEST
    }

    public static long getNativeTransportMaxConcurrentConnectionsPerIp()
    {
        logger.warn("[CTEST][GET-PARAM] " + "native_transport_max_concurrent_connections_per_ip" ); //CTEST
        return conf.native_transport_max_concurrent_connections_per_ip;
    }

    public static void setNativeTransportMaxConcurrentConnectionsPerIp(long native_transport_max_concurrent_connections_per_ip)
    {
        conf.native_transport_max_concurrent_connections_per_ip = native_transport_max_concurrent_connections_per_ip;
        logger.warn("[CTEST][SET-PARAM] " + "native_transport_max_concurrent_connections_per_ip" + getStackTrace()); //CTEST
    }

    public static boolean useNativeTransportLegacyFlusher()
    {
        logger.warn("[CTEST][GET-PARAM] " + "native_transport_flush_in_batches_legacy" ); //CTEST
        return conf.native_transport_flush_in_batches_legacy;
    }

    public static boolean getNativeTransportAllowOlderProtocols()
    {
        logger.warn("[CTEST][GET-PARAM] " + "native_transport_allow_older_protocols" ); //CTEST
        return conf.native_transport_allow_older_protocols;
    }

    public static void setNativeTransportAllowOlderProtocols(boolean isEnabled)
    {
        conf.native_transport_allow_older_protocols = isEnabled;
        logger.warn("[CTEST][SET-PARAM] " + "native_transport_allow_older_protocols" + getStackTrace()); //CTEST
    }

    public static double getCommitLogSyncGroupWindow()
    {
        logger.warn("[CTEST][GET-PARAM] " + "commitlog_sync_group_window_in_ms" ); //CTEST
        return conf.commitlog_sync_group_window_in_ms;
    }

    public static void setCommitLogSyncGroupWindow(double windowMillis)
    {
        conf.commitlog_sync_group_window_in_ms = windowMillis;
        logger.warn("[CTEST][SET-PARAM] " + "commitlog_sync_group_window_in_ms" + getStackTrace()); //CTEST
    }

    public static int getNativeTransportReceiveQueueCapacityInBytes()
    {
        logger.warn("[CTEST][GET-PARAM] " + "native_transport_receive_queue_capacity_in_bytes" ); //CTEST
        return conf.native_transport_receive_queue_capacity_in_bytes;
    }

    public static void setNativeTransportReceiveQueueCapacityInBytes(int queueSize)
    {
        conf.native_transport_receive_queue_capacity_in_bytes = queueSize;
        logger.warn("[CTEST][SET-PARAM] " + "native_transport_receive_queue_capacity_in_bytes" + getStackTrace()); //CTEST
    }

    public static long getNativeTransportMaxConcurrentRequestsInBytesPerIp()
    {
        logger.warn("[CTEST][GET-PARAM] " + "native_transport_max_concurrent_requests_in_bytes_per_ip" ); //CTEST
        return conf.native_transport_max_concurrent_requests_in_bytes_per_ip;
    }

    public static void setNativeTransportMaxConcurrentRequestsInBytesPerIp(long maxConcurrentRequestsInBytes)
    {
        conf.native_transport_max_concurrent_requests_in_bytes_per_ip = maxConcurrentRequestsInBytes;
        logger.warn("[CTEST][SET-PARAM] " + "native_transport_max_concurrent_requests_in_bytes_per_ip" + getStackTrace()); //CTEST
    }

    public static long getNativeTransportMaxConcurrentRequestsInBytes()
    {
        logger.warn("[CTEST][GET-PARAM] " + "native_transport_max_concurrent_requests_in_bytes" ); //CTEST
        return conf.native_transport_max_concurrent_requests_in_bytes;
    }

    public static void setNativeTransportMaxConcurrentRequestsInBytes(long maxConcurrentRequestsInBytes)
    {
        conf.native_transport_max_concurrent_requests_in_bytes = maxConcurrentRequestsInBytes;
        logger.warn("[CTEST][SET-PARAM] " + "native_transport_max_concurrent_requests_in_bytes" + getStackTrace()); //CTEST
    }

    public static int getCommitLogSyncPeriod()
    {
        logger.warn("[CTEST][GET-PARAM] " + "commitlog_sync_period_in_ms" ); //CTEST
        return conf.commitlog_sync_period_in_ms;
    }

    public static long getPeriodicCommitLogSyncBlock()
    {
        logger.warn("[CTEST][GET-PARAM] " + "periodic_commitlog_sync_lag_block_in_ms" ); //CTEST
        Integer blockMillis = conf.periodic_commitlog_sync_lag_block_in_ms;
        return blockMillis == null
               ? (long)(getCommitLogSyncPeriod() * 1.5)
               : blockMillis;
    }

    public static void setCommitLogSyncPeriod(int periodMillis)
    {
        conf.commitlog_sync_period_in_ms = periodMillis;
        logger.warn("[CTEST][SET-PARAM] " + "commitlog_sync_period_in_ms" + getStackTrace()); //CTEST
    }

    public static Config.CommitLogSync getCommitLogSync()
    {
        logger.warn("[CTEST][GET-PARAM] " + "commitlog_sync" ); //CTEST
        return conf.commitlog_sync;
    }

    public static void setCommitLogSync(CommitLogSync sync)
    {
        conf.commitlog_sync = sync;
        logger.warn("[CTEST][SET-PARAM] " + "commitlog_sync" + getStackTrace()); //CTEST
    }

    public static Config.DiskAccessMode getDiskAccessMode()
    {
        logger.warn("[CTEST][GET-PARAM] " + "disk_access_mode" ); //CTEST
        return conf.disk_access_mode;
    }

    // Do not use outside unit tests.
    @VisibleForTesting
    public static void setDiskAccessMode(Config.DiskAccessMode mode)
    {
        conf.disk_access_mode = mode;
        logger.warn("[CTEST][SET-PARAM] " + "disk_access_mode" + getStackTrace()); //CTEST
    }

    public static Config.DiskAccessMode getIndexAccessMode()
    {
        return indexAccessMode;
    }

    // Do not use outside unit tests.
    @VisibleForTesting
    public static void setIndexAccessMode(Config.DiskAccessMode mode)
    {
        indexAccessMode = mode;
    }

    public static void setDiskFailurePolicy(Config.DiskFailurePolicy policy)
    {
        conf.disk_failure_policy = policy;
        logger.warn("[CTEST][SET-PARAM] " + "disk_failure_policy" + getStackTrace()); //CTEST
    }

    public static Config.DiskFailurePolicy getDiskFailurePolicy()
    {
        logger.warn("[CTEST][GET-PARAM] " + "disk_failure_policy" ); //CTEST
        return conf.disk_failure_policy;
    }

    public static void setCommitFailurePolicy(Config.CommitFailurePolicy policy)
    {
        conf.commit_failure_policy = policy;
        logger.warn("[CTEST][SET-PARAM] " + "commit_failure_policy" + getStackTrace()); //CTEST
    }

    public static Config.CommitFailurePolicy getCommitFailurePolicy()
    {
        logger.warn("[CTEST][GET-PARAM] " + "commit_failure_policy" ); //CTEST
        return conf.commit_failure_policy;
    }

    public static boolean isSnapshotBeforeCompaction()
    {
        logger.warn("[CTEST][GET-PARAM] " + "snapshot_before_compaction" ); //CTEST
        return conf.snapshot_before_compaction;
    }

    public static boolean isAutoSnapshot()
    {
        logger.warn("[CTEST][GET-PARAM] " + "auto_snapshot" ); //CTEST
        return conf.auto_snapshot;
    }

    @VisibleForTesting
    public static void setAutoSnapshot(boolean autoSnapshot)
    {
        conf.auto_snapshot = autoSnapshot;
        logger.warn("[CTEST][SET-PARAM] " + "auto_snapshot" + getStackTrace()); //CTEST
    }
    @VisibleForTesting
    public static boolean getAutoSnapshot()
    {
        logger.warn("[CTEST][GET-PARAM] " + "auto_snapshot" ); //CTEST
        return conf.auto_snapshot;
    }

    public static long getSnapshotLinksPerSecond()
    {
        logger.warn("[CTEST][GET-PARAM] " + "snapshot_links_per_second" ); //CTEST
        return conf.snapshot_links_per_second == 0 ? Long.MAX_VALUE : conf.snapshot_links_per_second;
    }

    public static void setSnapshotLinksPerSecond(long throttle)
    {
        if (throttle < 0)
            throw new IllegalArgumentException("Invalid throttle for snapshot_links_per_second: must be positive");

        conf.snapshot_links_per_second = throttle;
        logger.warn("[CTEST][SET-PARAM] " + "snapshot_links_per_second" + getStackTrace()); //CTEST
    }

    public static RateLimiter getSnapshotRateLimiter()
    {
        return RateLimiter.create(getSnapshotLinksPerSecond());
    }

    public static boolean isAutoBootstrap()
    {
        logger.warn("[CTEST][GET-PARAM] " + "auto_bootstrap" ); //CTEST
        return Boolean.parseBoolean(System.getProperty(Config.PROPERTY_PREFIX + "auto_bootstrap", Boolean.toString(conf.auto_bootstrap)));
    }

    public static void setHintedHandoffEnabled(boolean hintedHandoffEnabled)
    {
        conf.hinted_handoff_enabled = hintedHandoffEnabled;
        logger.warn("[CTEST][SET-PARAM] " + "hinted_handoff_enabled" + getStackTrace()); //CTEST
    }

    public static boolean hintedHandoffEnabled()
    {
        logger.warn("[CTEST][GET-PARAM] " + "hinted_handoff_enabled" ); //CTEST
        return conf.hinted_handoff_enabled;
    }

    public static Set<String> hintedHandoffDisabledDCs()
    {
        logger.warn("[CTEST][GET-PARAM] " + "hinted_handoff_disabled_datacenters" ); //CTEST
        return conf.hinted_handoff_disabled_datacenters;
    }

    public static void enableHintsForDC(String dc)
    {
        conf.hinted_handoff_disabled_datacenters.remove(dc);
        logger.warn("[CTEST][SET-PARAM] " + "hinted_handoff_disabled_datacenters" + getStackTrace()); //CTEST
    }

    public static void disableHintsForDC(String dc)
    {
        conf.hinted_handoff_disabled_datacenters.add(dc);
        logger.warn("[CTEST][SET-PARAM] " + "hinted_handoff_disabled_datacenters" + getStackTrace()); //CTEST
    }

    public static void setMaxHintWindow(int ms)
    {
        conf.max_hint_window_in_ms = ms;
        logger.warn("[CTEST][SET-PARAM] " + "max_hint_window_in_ms" + getStackTrace()); //CTEST
    }

    public static int getMaxHintWindow()
    {
        logger.warn("[CTEST][GET-PARAM] " + "max_hint_window_in_ms" ); //CTEST
        return conf.max_hint_window_in_ms;
    }

    public static File getHintsDirectory()
    {
        logger.warn("[CTEST][GET-PARAM] " + "hints_directory" ); //CTEST
        return new File(conf.hints_directory);
    }

    public static File getSerializedCachePath(CacheType cacheType, String version, String extension)
    {
        logger.warn("[CTEST][GET-PARAM] " + "saved_caches_directory" ); //CTEST
        String name = cacheType.toString()
                + (version == null ? "" : '-' + version + '.' + extension);
        return new File(conf.saved_caches_directory, name);
    }

    public static int getDynamicUpdateInterval()
    {
        logger.warn("[CTEST][GET-PARAM] " + "dynamic_snitch_update_interval_in_ms" ); //CTEST
        return conf.dynamic_snitch_update_interval_in_ms;
    }
    public static void setDynamicUpdateInterval(int dynamicUpdateInterval)
    {
        conf.dynamic_snitch_update_interval_in_ms = dynamicUpdateInterval;
        logger.warn("[CTEST][SET-PARAM] " + "dynamic_snitch_update_interval_in_ms" + getStackTrace()); //CTEST
    }

    public static int getDynamicResetInterval()
    {
        logger.warn("[CTEST][GET-PARAM] " + "dynamic_snitch_reset_interval_in_ms" ); //CTEST
        return conf.dynamic_snitch_reset_interval_in_ms;
    }
    public static void setDynamicResetInterval(int dynamicResetInterval)
    {
        conf.dynamic_snitch_reset_interval_in_ms = dynamicResetInterval;
        logger.warn("[CTEST][SET-PARAM] " + "dynamic_snitch_reset_interval_in_ms" + getStackTrace()); //CTEST
    }

    public static double getDynamicBadnessThreshold()
    {
        logger.warn("[CTEST][GET-PARAM] " + "dynamic_snitch_badness_threshold" ); //CTEST
        return conf.dynamic_snitch_badness_threshold;
    }

    public static void setDynamicBadnessThreshold(double dynamicBadnessThreshold)
    {
        conf.dynamic_snitch_badness_threshold = dynamicBadnessThreshold;
        logger.warn("[CTEST][SET-PARAM] " + "dynamic_snitch_badness_threshold" + getStackTrace()); //CTEST
    }

    public static EncryptionOptions.ServerEncryptionOptions getInternodeMessagingEncyptionOptions()
    {
        logger.warn("[CTEST][GET-PARAM] " + "server_encryption_options" ); //CTEST
        return conf.server_encryption_options;
    }

    public static void setInternodeMessagingEncyptionOptions(EncryptionOptions.ServerEncryptionOptions encryptionOptions)
    {
        conf.server_encryption_options = encryptionOptions;
        logger.warn("[CTEST][SET-PARAM] " + "server_encryption_options" + getStackTrace()); //CTEST
    }

    public static EncryptionOptions getNativeProtocolEncryptionOptions()
    {
        logger.warn("[CTEST][GET-PARAM] " + "client_encryption_options" ); //CTEST
        return conf.client_encryption_options;
    }

    @VisibleForTesting
    public static void updateNativeProtocolEncryptionOptions(Function<EncryptionOptions, EncryptionOptions> update)
    {
        conf.client_encryption_options = update.apply(conf.client_encryption_options);
        logger.warn("[CTEST][SET-PARAM] " + "client_encryption_options" + getStackTrace()); //CTEST
    }

    public static int getHintedHandoffThrottleInKB()
    {
        logger.warn("[CTEST][GET-PARAM] " + "hinted_handoff_throttle_in_kb" ); //CTEST
        return conf.hinted_handoff_throttle_in_kb;
    }

    public static void setHintedHandoffThrottleInKB(int throttleInKB)
    {
        conf.hinted_handoff_throttle_in_kb = throttleInKB;
        logger.warn("[CTEST][SET-PARAM] " + "hinted_handoff_throttle_in_kb" + getStackTrace()); //CTEST
    }

    public static int getBatchlogReplayThrottleInKB()
    {
        logger.warn("[CTEST][GET-PARAM] " + "batchlog_replay_throttle_in_kb" ); //CTEST
        return conf.batchlog_replay_throttle_in_kb;
    }

    public static void setBatchlogReplayThrottleInKB(int throttleInKB)
    {
        conf.batchlog_replay_throttle_in_kb = throttleInKB;
        logger.warn("[CTEST][SET-PARAM] " + "batchlog_replay_throttle_in_kb" + getStackTrace()); //CTEST
    }

    public static int getMaxHintsDeliveryThreads()
    {
        logger.warn("[CTEST][GET-PARAM] " + "max_hints_delivery_threads" ); //CTEST
        return conf.max_hints_delivery_threads;
    }

    public static int getHintsFlushPeriodInMS()
    {
        logger.warn("[CTEST][GET-PARAM] " + "hints_flush_period_in_ms" ); //CTEST
        return conf.hints_flush_period_in_ms;
    }

    public static long getMaxHintsFileSize()
    {
        return  ByteUnit.MEBI_BYTES.toBytes(conf.max_hints_file_size_in_mb);
    }

    public static ParameterizedClass getHintsCompression()
    {
        logger.warn("[CTEST][GET-PARAM] " + "hints_compression" ); //CTEST
        return conf.hints_compression;
    }

    public static void setHintsCompression(ParameterizedClass parameterizedClass)
    {
        conf.hints_compression = parameterizedClass;
        logger.warn("[CTEST][SET-PARAM] " + "hints_compression" + getStackTrace()); //CTEST
    }

    public static boolean isIncrementalBackupsEnabled()
    {
        logger.warn("[CTEST][GET-PARAM] " + "incremental_backups" ); //CTEST
        return conf.incremental_backups;
    }

    public static void setIncrementalBackupsEnabled(boolean value)
    {
        conf.incremental_backups = value;
        logger.warn("[CTEST][SET-PARAM] " + "incremental_backups" + getStackTrace()); //CTEST
    }

    public static boolean getFileCacheEnabled()
    {
        logger.warn("[CTEST][GET-PARAM] " + "file_cache_enabled" ); //CTEST
        return conf.file_cache_enabled;
    }

    public static int getFileCacheSizeInMB()
    {
        if (conf.file_cache_size_in_mb == null)
        {
            // In client mode the value is not set.
            assert DatabaseDescriptor.isClientInitialized();
            return 0;
        }

        logger.warn("[CTEST][GET-PARAM] " + "file_cache_size_in_mb" ); //CTEST
        return conf.file_cache_size_in_mb;
    }

    public static int getNetworkingCacheSizeInMB()
    {
        if (conf.networking_cache_size_in_mb == null)
        {
            // In client mode the value is not set.
            assert DatabaseDescriptor.isClientInitialized();
            return 0;
        }
        logger.warn("[CTEST][GET-PARAM] " + "networking_cache_size_in_mb" ); //CTEST
        return conf.networking_cache_size_in_mb;
    }

    public static boolean getFileCacheRoundUp()
    {
        if (conf.file_cache_round_up == null)
        {
            // In client mode the value is not set.
            assert DatabaseDescriptor.isClientInitialized();
            return false;
        }

        logger.warn("[CTEST][GET-PARAM] " + "file_cache_round_up" ); //CTEST
        return conf.file_cache_round_up;
    }

    public static DiskOptimizationStrategy getDiskOptimizationStrategy()
    {
        return diskOptimizationStrategy;
    }

    public static double getDiskOptimizationEstimatePercentile()
    {
        logger.warn("[CTEST][GET-PARAM] " + "disk_optimization_estimate_percentile" ); //CTEST
        return conf.disk_optimization_estimate_percentile;
    }

    public static long getTotalCommitlogSpaceInMB()
    {
        logger.warn("[CTEST][GET-PARAM] " + "commitlog_total_space_in_mb" ); //CTEST
        return conf.commitlog_total_space_in_mb;
    }

    public static boolean shouldMigrateKeycacheOnCompaction()
    {
        logger.warn("[CTEST][GET-PARAM] " + "key_cache_migrate_during_compaction" ); //CTEST
        return conf.key_cache_migrate_during_compaction;
    }

    public static void setMigrateKeycacheOnCompaction(boolean migrateCacheEntry)
    {
        conf.key_cache_migrate_during_compaction = migrateCacheEntry;
        logger.warn("[CTEST][SET-PARAM] " + "key_cache_migrate_during_compaction" + getStackTrace()); //CTEST
    }

    public static int getSSTablePreemptiveOpenIntervalInMB()
    {
        logger.warn("[CTEST][GET-PARAM] " + "sstable_preemptive_open_interval_in_mb" ); //CTEST
        return FBUtilities.isWindows ? -1 : conf.sstable_preemptive_open_interval_in_mb;
    }
    public static void setSSTablePreemptiveOpenIntervalInMB(int mb)
    {
        conf.sstable_preemptive_open_interval_in_mb = mb;
        logger.warn("[CTEST][SET-PARAM] " + "sstable_preemptive_open_interval_in_mb" + getStackTrace()); //CTEST
    }

    public static boolean getTrickleFsync()
    {
        logger.warn("[CTEST][GET-PARAM] " + "trickle_fsync" ); //CTEST
        return conf.trickle_fsync;
    }

    public static int getTrickleFsyncIntervalInKb()
    {
        logger.warn("[CTEST][GET-PARAM] " + "trickle_fsync_interval_in_kb" ); //CTEST
        return conf.trickle_fsync_interval_in_kb;
    }

    public static long getKeyCacheSizeInMB()
    {
        return keyCacheSizeInMB;
    }

    public static long getIndexSummaryCapacityInMB()
    {
        return indexSummaryCapacityInMB;
    }

    public static int getKeyCacheSavePeriod()
    {
        logger.warn("[CTEST][GET-PARAM] " + "key_cache_save_period" ); //CTEST
        return conf.key_cache_save_period;
    }

    public static void setKeyCacheSavePeriod(int keyCacheSavePeriod)
    {
        conf.key_cache_save_period = keyCacheSavePeriod;
        logger.warn("[CTEST][SET-PARAM] " + "key_cache_save_period" + getStackTrace()); //CTEST
    }

    public static int getKeyCacheKeysToSave()
    {
        logger.warn("[CTEST][GET-PARAM] " + "key_cache_keys_to_save" ); //CTEST
        return conf.key_cache_keys_to_save;
    }

    public static void setKeyCacheKeysToSave(int keyCacheKeysToSave)
    {
        conf.key_cache_keys_to_save = keyCacheKeysToSave;
        logger.warn("[CTEST][SET-PARAM] " + "key_cache_keys_to_save" + getStackTrace()); //CTEST
    }

    public static String getRowCacheClassName()
    {
        logger.warn("[CTEST][GET-PARAM] " + "row_cache_class_name" ); //CTEST
        return conf.row_cache_class_name;
    }

    public static long getRowCacheSizeInMB()
    {
        logger.warn("[CTEST][GET-PARAM] " + "row_cache_size_in_mb" ); //CTEST
        return conf.row_cache_size_in_mb;
    }

    @VisibleForTesting
    public static void setRowCacheSizeInMB(long val)
    {
        conf.row_cache_size_in_mb = val;
        logger.warn("[CTEST][SET-PARAM] " + "row_cache_size_in_mb" + getStackTrace()); //CTEST
    }

    public static int getRowCacheSavePeriod()
    {
        logger.warn("[CTEST][GET-PARAM] " + "row_cache_save_period" ); //CTEST
        return conf.row_cache_save_period;
    }

    public static void setRowCacheSavePeriod(int rowCacheSavePeriod)
    {
        conf.row_cache_save_period = rowCacheSavePeriod;
        logger.warn("[CTEST][SET-PARAM] " + "row_cache_save_period" + getStackTrace()); //CTEST
    }

    public static int getRowCacheKeysToSave()
    {
        logger.warn("[CTEST][GET-PARAM] " + "row_cache_keys_to_save" ); //CTEST
        return conf.row_cache_keys_to_save;
    }

    public static long getCounterCacheSizeInMB()
    {
        return counterCacheSizeInMB;
    }

    public static void setRowCacheKeysToSave(int rowCacheKeysToSave)
    {
        conf.row_cache_keys_to_save = rowCacheKeysToSave;
        logger.warn("[CTEST][SET-PARAM] " + "row_cache_keys_to_save" + getStackTrace()); //CTEST
    }

    public static int getCounterCacheSavePeriod()
    {
        logger.warn("[CTEST][GET-PARAM] " + "counter_cache_save_period" ); //CTEST
        return conf.counter_cache_save_period;
    }

    public static void setCounterCacheSavePeriod(int counterCacheSavePeriod)
    {
        conf.counter_cache_save_period = counterCacheSavePeriod;
        logger.warn("[CTEST][SET-PARAM] " + "counter_cache_save_period" + getStackTrace()); //CTEST
    }

    public static int getCacheLoadTimeout()
    {
        logger.warn("[CTEST][GET-PARAM] " + "cache_load_timeout_seconds" ); //CTEST
        return conf.cache_load_timeout_seconds;
    }

    @VisibleForTesting
    public static void setCacheLoadTimeout(int seconds)
    {
        conf.cache_load_timeout_seconds = seconds;
        logger.warn("[CTEST][SET-PARAM] " + "cache_load_timeout_seconds" + getStackTrace()); //CTEST
    }

    public static int getCounterCacheKeysToSave()
    {
        logger.warn("[CTEST][GET-PARAM] " + "counter_cache_keys_to_save" ); //CTEST
        return conf.counter_cache_keys_to_save;
    }

    public static void setCounterCacheKeysToSave(int counterCacheKeysToSave)
    {
        conf.counter_cache_keys_to_save = counterCacheKeysToSave;
        logger.warn("[CTEST][SET-PARAM] " + "counter_cache_keys_to_save" + getStackTrace()); //CTEST
    }

    public static int getStreamingKeepAlivePeriod()
    {
        logger.warn("[CTEST][GET-PARAM] " + "streaming_keep_alive_period_in_secs" ); //CTEST
        return conf.streaming_keep_alive_period_in_secs;
    }

    public static int getStreamingConnectionsPerHost()
    {
        logger.warn("[CTEST][GET-PARAM] " + "streaming_connections_per_host" ); //CTEST
        return conf.streaming_connections_per_host;
    }

    public static boolean streamEntireSSTables()
    {
        logger.warn("[CTEST][GET-PARAM] " + "stream_entire_sstables" ); //CTEST
        return conf.stream_entire_sstables;
    }

    public static String getLocalDataCenter()
    {
        return localDC;
    }

    public static Comparator<Replica> getLocalComparator()
    {
        logger.warn("[CTEST][GET-PARAM] " + "localComparator" ); //CTEST
        return localComparator;
    }

    public static Config.InternodeCompression internodeCompression()
    {
        logger.warn("[CTEST][GET-PARAM] " + "internode_compression" ); //CTEST
        return conf.internode_compression;
    }

    public static void setInternodeCompression(Config.InternodeCompression compression)
    {
        conf.internode_compression = compression;
        logger.warn("[CTEST][SET-PARAM] " + "internode_compression" + getStackTrace()); //CTEST
    }

    public static boolean getInterDCTcpNoDelay()
    {
        logger.warn("[CTEST][GET-PARAM] " + "inter_dc_tcp_nodelay" ); //CTEST
        return conf.inter_dc_tcp_nodelay;
    }

    public static long getMemtableHeapSpaceInMb()
    {
        logger.warn("[CTEST][GET-PARAM] " + "memtable_heap_space_in_mb" ); //CTEST
        return conf.memtable_heap_space_in_mb;
    }

    public static long getMemtableOffheapSpaceInMb()
    {
        logger.warn("[CTEST][GET-PARAM] " + "memtable_offheap_space_in_mb" ); //CTEST
        return conf.memtable_offheap_space_in_mb;
    }

    public static Config.MemtableAllocationType getMemtableAllocationType()
    {
        logger.warn("[CTEST][GET-PARAM] " + "memtable_allocation_type" ); //CTEST
        return conf.memtable_allocation_type;
    }

    public static int getRepairSessionMaxTreeDepth()
    {
        logger.warn("[CTEST][GET-PARAM] " + "repair_session_max_tree_depth" ); //CTEST
        return conf.repair_session_max_tree_depth;
    }

    public static void setRepairSessionMaxTreeDepth(int depth)
    {
        if (depth < 10)
            throw new ConfigurationException("Cannot set repair_session_max_tree_depth to " + depth +
                                             " which is < 10, doing nothing");
        else if (depth > 20)
            logger.warn("repair_session_max_tree_depth of " + depth + " > 20 could lead to excessive memory usage");

        conf.repair_session_max_tree_depth = depth;
        logger.warn("[CTEST][SET-PARAM] " + "repair_session_max_tree_depth" + getStackTrace()); //CTEST
    }

    public static int getRepairSessionSpaceInMegabytes()
    {
        logger.warn("[CTEST][GET-PARAM] " + "repair_session_space_in_mb" ); //CTEST
        return conf.repair_session_space_in_mb;
    }

    public static void setRepairSessionSpaceInMegabytes(int sizeInMegabytes)
    {
        if (sizeInMegabytes < 1)
            throw new ConfigurationException("Cannot set repair_session_space_in_mb to " + sizeInMegabytes +
                                             " < 1 megabyte");
        else if (sizeInMegabytes > (int) (Runtime.getRuntime().maxMemory() / (4 * 1048576)))
            logger.warn("A repair_session_space_in_mb of " + conf.repair_session_space_in_mb +
                        " megabytes is likely to cause heap pressure.");

        conf.repair_session_space_in_mb = sizeInMegabytes;
        logger.warn("[CTEST][SET-PARAM] " + "repair_session_space_in_mb" + getStackTrace()); //CTEST
    }

    public static Float getMemtableCleanupThreshold()
    {
        logger.warn("[CTEST][GET-PARAM] " + "memtable_cleanup_threshold" ); //CTEST
        return conf.memtable_cleanup_threshold;
    }

    public static int getIndexSummaryResizeIntervalInMinutes()
    {
        logger.warn("[CTEST][GET-PARAM] " + "index_summary_resize_interval_in_minutes" ); //CTEST
        return conf.index_summary_resize_interval_in_minutes;
    }

    public static void setIndexSummaryResizeIntervalInMinutes(int value)
    {
        conf.index_summary_resize_interval_in_minutes = value;
        logger.warn("[CTEST][SET-PARAM] " + "index_summary_resize_interval_in_minutes" + getStackTrace()); //CTEST
    }

    public static boolean hasLargeAddressSpace()
    {
        // currently we just check if it's a 64bit arch, but any we only really care if the address space is large
        String datamodel = SUN_ARCH_DATA_MODEL.getString();
        if (datamodel != null)
        {
            switch (datamodel)
            {
                case "64": return true;
                case "32": return false;
            }
        }
        String arch = OS_ARCH.getString();
        return arch.contains("64") || arch.contains("sparcv9");
    }

    public static int getTracetypeRepairTTL()
    {
        logger.warn("[CTEST][GET-PARAM] " + "tracetype_repair_ttl" ); //CTEST
        return conf.tracetype_repair_ttl;
    }

    public static int getTracetypeQueryTTL()
    {
        logger.warn("[CTEST][GET-PARAM] " + "tracetype_query_ttl" ); //CTEST
        return conf.tracetype_query_ttl;
    }

    public static int getWindowsTimerInterval()
    {
        logger.warn("[CTEST][GET-PARAM] " + "windows_timer_interval" ); //CTEST
        return conf.windows_timer_interval;
    }

    public static long getPreparedStatementsCacheSizeMB()
    {
        return preparedStatementsCacheSizeInMB;
    }

    public static boolean enableUserDefinedFunctions()
    {
        logger.warn("[CTEST][GET-PARAM] " + "enable_user_defined_functions" ); //CTEST
        return conf.enable_user_defined_functions;
    }

    public static boolean enableScriptedUserDefinedFunctions()
    {
        logger.warn("[CTEST][GET-PARAM] " + "enable_scripted_user_defined_functions" ); //CTEST
        return conf.enable_scripted_user_defined_functions;
    }

    public static void enableScriptedUserDefinedFunctions(boolean enableScriptedUserDefinedFunctions)
    {
        conf.enable_scripted_user_defined_functions = enableScriptedUserDefinedFunctions;
        logger.warn("[CTEST][SET-PARAM] " + "enable_scripted_user_defined_functions" + getStackTrace()); //CTEST
    }

    public static boolean enableUserDefinedFunctionsThreads()
    {
        logger.warn("[CTEST][GET-PARAM] " + "enable_user_defined_functions_threads" ); //CTEST
        return conf.enable_user_defined_functions_threads;
    }

    public static long getUserDefinedFunctionWarnTimeout()
    {
        logger.warn("[CTEST][GET-PARAM] " + "user_defined_function_warn_timeout" ); //CTEST
        return conf.user_defined_function_warn_timeout;
    }

    public static void setUserDefinedFunctionWarnTimeout(long userDefinedFunctionWarnTimeout)
    {
        conf.user_defined_function_warn_timeout = userDefinedFunctionWarnTimeout;
        logger.warn("[CTEST][SET-PARAM] " + "user_defined_function_warn_timeout" + getStackTrace()); //CTEST
    }

    public static boolean allowInsecureUDFs()
    {
        logger.warn("[CTEST][GET-PARAM] " + "allow_insecure_udfs" ); //CTEST
        return conf.allow_insecure_udfs;
    }

    public static boolean allowExtraInsecureUDFs()
    {
        logger.warn("[CTEST][GET-PARAM] " + "allow_extra_insecure_udfs" ); //CTEST
        return conf.allow_extra_insecure_udfs;
    }

    public static boolean getEnableMaterializedViews()
    {
        logger.warn("[CTEST][GET-PARAM] " + "enable_materialized_views" ); //CTEST
        return conf.enable_materialized_views;
    }

    public static void setEnableMaterializedViews(boolean enableMaterializedViews)
    {
        conf.enable_materialized_views = enableMaterializedViews;
        logger.warn("[CTEST][SET-PARAM] " + "enable_materialized_views" + getStackTrace()); //CTEST
    }

    public static boolean getEnableSASIIndexes()
    {
        logger.warn("[CTEST][GET-PARAM] " + "enable_sasi_indexes" ); //CTEST
        return conf.enable_sasi_indexes;
    }

    public static void setEnableSASIIndexes(boolean enableSASIIndexes)
    {
        conf.enable_sasi_indexes = enableSASIIndexes;
        logger.warn("[CTEST][SET-PARAM] " + "enable_sasi_indexes" + getStackTrace()); //CTEST
    }

    public static boolean isTransientReplicationEnabled()
    {
        logger.warn("[CTEST][GET-PARAM] " + "enable_transient_replication" ); //CTEST
        return conf.enable_transient_replication;
    }

    public static void setTransientReplicationEnabledUnsafe(boolean enabled)
    {
        conf.enable_transient_replication = enabled;
        logger.warn("[CTEST][SET-PARAM] " + "enable_transient_replication" + getStackTrace()); //CTEST
    }

    public static boolean enableDropCompactStorage()
    {
        logger.warn("[CTEST][GET-PARAM] " + "enable_drop_compact_storage" ); //CTEST
        return conf.enable_drop_compact_storage;
    }

    @VisibleForTesting
    public static void setEnableDropCompactStorage(boolean enableDropCompactStorage)
    {
        conf.enable_drop_compact_storage = enableDropCompactStorage;
        logger.warn("[CTEST][SET-PARAM] " + "enable_drop_compact_storage" + getStackTrace()); //CTEST
    }

    public static long getUserDefinedFunctionFailTimeout()
    {
        logger.warn("[CTEST][GET-PARAM] " + "user_defined_function_fail_timeout" ); //CTEST
        return conf.user_defined_function_fail_timeout;
    }

    public static void setUserDefinedFunctionFailTimeout(long userDefinedFunctionFailTimeout)
    {
        conf.user_defined_function_fail_timeout = userDefinedFunctionFailTimeout;
        logger.warn("[CTEST][SET-PARAM] " + "user_defined_function_fail_timeout" + getStackTrace()); //CTEST
    }

    public static Config.UserFunctionTimeoutPolicy getUserFunctionTimeoutPolicy()
    {
        logger.warn("[CTEST][GET-PARAM] " + "user_function_timeout_policy" ); //CTEST
        return conf.user_function_timeout_policy;
    }

    public static void setUserFunctionTimeoutPolicy(Config.UserFunctionTimeoutPolicy userFunctionTimeoutPolicy)
    {
        conf.user_function_timeout_policy = userFunctionTimeoutPolicy;
        logger.warn("[CTEST][SET-PARAM] " + "user_function_timeout_policy" + getStackTrace()); //CTEST
    }

    public static long getGCLogThreshold()
    {
        logger.warn("[CTEST][GET-PARAM] " + "gc_log_threshold_in_ms" ); //CTEST
        return conf.gc_log_threshold_in_ms;
    }

    public static void setGCLogThreshold(int gcLogThreshold)
    {
        conf.gc_log_threshold_in_ms = gcLogThreshold;
        logger.warn("[CTEST][SET-PARAM] " + "gc_log_threshold_in_ms" + getStackTrace()); //CTEST
    }

    public static EncryptionContext getEncryptionContext()
    {
        return encryptionContext;
    }

    public static long getGCWarnThreshold()
    {
        logger.warn("[CTEST][GET-PARAM] " + "gc_warn_threshold_in_ms" ); //CTEST
        return conf.gc_warn_threshold_in_ms;
    }

    public static void setGCWarnThreshold(int threshold)
    {
        conf.gc_warn_threshold_in_ms = threshold;
        logger.warn("[CTEST][SET-PARAM] " + "gc_warn_threshold_in_ms" + getStackTrace()); //CTEST
    }

    public static boolean isCDCEnabled()
    {
        logger.warn("[CTEST][GET-PARAM] " + "cdc_enabled" ); //CTEST
        return conf.cdc_enabled;
    }

    @VisibleForTesting
    public static void setCDCEnabled(boolean cdc_enabled)
    {
        conf.cdc_enabled = cdc_enabled;
        logger.warn("[CTEST][SET-PARAM] " + "cdc_enabled" + getStackTrace()); //CTEST
    }

    public static String getCDCLogLocation()
    {
        logger.warn("[CTEST][GET-PARAM] " + "cdc_raw_directory" ); //CTEST
        return conf.cdc_raw_directory;
    }

    public static int getCDCSpaceInMB()
    {
        logger.warn("[CTEST][GET-PARAM] " + "cdc_total_space_in_mb" ); //CTEST
        return conf.cdc_total_space_in_mb;
    }

    @VisibleForTesting
    public static void setCDCSpaceInMB(int input)
    {
        conf.cdc_total_space_in_mb = input;
        logger.warn("[CTEST][SET-PARAM] " + "cdc_total_space_in_mb" + getStackTrace()); //CTEST
    }

    public static int getCDCDiskCheckInterval()
    {
        logger.warn("[CTEST][GET-PARAM] " + "cdc_free_space_check_interval_ms" ); //CTEST
        return conf.cdc_free_space_check_interval_ms;
    }

    @VisibleForTesting
    public static void setEncryptionContext(EncryptionContext ec)
    {
        encryptionContext = ec;
    }

    public static int searchConcurrencyFactor()
    {
        return searchConcurrencyFactor;
    }

    public static boolean isUnsafeSystem()
    {
        return unsafeSystem;
    }

    public static boolean diagnosticEventsEnabled()
    {
        logger.warn("[CTEST][GET-PARAM] " + "diagnostic_events_enabled" ); //CTEST
        return conf.diagnostic_events_enabled;
    }

    public static void setDiagnosticEventsEnabled(boolean enabled)
    {
        conf.diagnostic_events_enabled = enabled;
        logger.warn("[CTEST][SET-PARAM] " + "diagnostic_events_enabled" + getStackTrace()); //CTEST
    }

    public static ConsistencyLevel getIdealConsistencyLevel()
    {
        logger.warn("[CTEST][GET-PARAM] " + "ideal_consistency_level" ); //CTEST
        return conf.ideal_consistency_level;
    }

    public static void setIdealConsistencyLevel(ConsistencyLevel cl)
    {
        conf.ideal_consistency_level = cl;
        logger.warn("[CTEST][SET-PARAM] " + "ideal_consistency_level" + getStackTrace()); //CTEST
    }

    public static int getRepairCommandPoolSize()
    {
        logger.warn("[CTEST][GET-PARAM] " + "repair_command_pool_size" ); //CTEST
        return conf.repair_command_pool_size;
    }

    public static Config.RepairCommandPoolFullStrategy getRepairCommandPoolFullStrategy()
    {
        logger.warn("[CTEST][GET-PARAM] " + "repair_command_pool_full_strategy" ); //CTEST
        return conf.repair_command_pool_full_strategy;
    }

    public static FullQueryLoggerOptions getFullQueryLogOptions()
    {
        logger.warn("[CTEST][GET-PARAM] " + "full_query_logging_options" ); //CTEST
        return  conf.full_query_logging_options;
    }

    public static boolean getBlockForPeersInRemoteDatacenters()
    {
        logger.warn("[CTEST][GET-PARAM] " + "block_for_peers_in_remote_dcs" ); //CTEST
        return conf.block_for_peers_in_remote_dcs;
    }

    public static int getBlockForPeersTimeoutInSeconds()
    {
        logger.warn("[CTEST][GET-PARAM] " + "block_for_peers_timeout_in_secs" ); //CTEST
        return conf.block_for_peers_timeout_in_secs;
    }

    public static boolean automaticSSTableUpgrade()
    {
        logger.warn("[CTEST][GET-PARAM] " + "automatic_sstable_upgrade" ); //CTEST
        return conf.automatic_sstable_upgrade;
    }

    public static void setAutomaticSSTableUpgradeEnabled(boolean enabled)
    {
        if (conf.automatic_sstable_upgrade != enabled)
            logger.debug("Changing automatic_sstable_upgrade to {}", enabled);
        conf.automatic_sstable_upgrade = enabled;
        logger.warn("[CTEST][SET-PARAM] " + "automatic_sstable_upgrade" + getStackTrace()); //CTEST
    }

    public static int maxConcurrentAutoUpgradeTasks()
    {
        logger.warn("[CTEST][GET-PARAM] " + "max_concurrent_automatic_sstable_upgrades" ); //CTEST
        return conf.max_concurrent_automatic_sstable_upgrades;
    }

    public static void setMaxConcurrentAutoUpgradeTasks(int value)
    {
        if (conf.max_concurrent_automatic_sstable_upgrades != value)
            logger.debug("Changing max_concurrent_automatic_sstable_upgrades to {}", value);
        validateMaxConcurrentAutoUpgradeTasksConf(value);
        conf.max_concurrent_automatic_sstable_upgrades = value;
        logger.warn("[CTEST][SET-PARAM] " + "max_concurrent_automatic_sstable_upgrades" + getStackTrace()); //CTEST
    }

    private static void validateMaxConcurrentAutoUpgradeTasksConf(int value)
    {
        if (value < 0)
            throw new ConfigurationException("max_concurrent_automatic_sstable_upgrades can't be negative");
        if (value > getConcurrentCompactors())
            logger.warn("max_concurrent_automatic_sstable_upgrades ({}) is larger than concurrent_compactors ({})", value, getConcurrentCompactors());
    }

    public static AuditLogOptions getAuditLoggingOptions()
    {
        logger.warn("[CTEST][GET-PARAM] " + "audit_logging_options" ); //CTEST
        return conf.audit_logging_options;
    }

    public static void setAuditLoggingOptions(AuditLogOptions auditLoggingOptions)
    {
        conf.audit_logging_options = auditLoggingOptions;
        logger.warn("[CTEST][SET-PARAM] " + "audit_logging_options" + getStackTrace()); //CTEST
    }

    public static Config.CorruptedTombstoneStrategy getCorruptedTombstoneStrategy()
    {
        logger.warn("[CTEST][GET-PARAM] " + "corrupted_tombstone_strategy" ); //CTEST
        return conf.corrupted_tombstone_strategy;
    }

    public static void setCorruptedTombstoneStrategy(Config.CorruptedTombstoneStrategy strategy)
    {
        conf.corrupted_tombstone_strategy = strategy;
        logger.warn("[CTEST][SET-PARAM] " + "corrupted_tombstone_strategy" + getStackTrace()); //CTEST
    }

    public static boolean getRepairedDataTrackingForRangeReadsEnabled()
    {
        logger.warn("[CTEST][GET-PARAM] " + "repaired_data_tracking_for_range_reads_enabled" ); //CTEST
        return conf.repaired_data_tracking_for_range_reads_enabled;
    }

    public static void setRepairedDataTrackingForRangeReadsEnabled(boolean enabled)
    {
        conf.repaired_data_tracking_for_range_reads_enabled = enabled;
        logger.warn("[CTEST][SET-PARAM] " + "repaired_data_tracking_for_range_reads_enabled" + getStackTrace()); //CTEST
    }

    public static boolean getRepairedDataTrackingForPartitionReadsEnabled()
    {
        logger.warn("[CTEST][GET-PARAM] " + "repaired_data_tracking_for_partition_reads_enabled" ); //CTEST
        return conf.repaired_data_tracking_for_partition_reads_enabled;
    }

    public static void setRepairedDataTrackingForPartitionReadsEnabled(boolean enabled)
    {
        conf.repaired_data_tracking_for_partition_reads_enabled = enabled;
        logger.warn("[CTEST][SET-PARAM] " + "repaired_data_tracking_for_partition_reads_enabled" + getStackTrace()); //CTEST
    }

    public static boolean snapshotOnRepairedDataMismatch()
    {
        logger.warn("[CTEST][GET-PARAM] " + "snapshot_on_repaired_data_mismatch" ); //CTEST
        return conf.snapshot_on_repaired_data_mismatch;
    }

    public static void setSnapshotOnRepairedDataMismatch(boolean enabled)
    {
        conf.snapshot_on_repaired_data_mismatch = enabled;
        logger.warn("[CTEST][SET-PARAM] " + "snapshot_on_repaired_data_mismatch" + getStackTrace()); //CTEST
    }

    public static boolean snapshotOnDuplicateRowDetection()
    {
        logger.warn("[CTEST][GET-PARAM] " + "snapshot_on_duplicate_row_detection" ); //CTEST
        return conf.snapshot_on_duplicate_row_detection;
    }

    public static void setSnapshotOnDuplicateRowDetection(boolean enabled)
    {
        conf.snapshot_on_duplicate_row_detection = enabled;
        logger.warn("[CTEST][SET-PARAM] " + "snapshot_on_duplicate_row_detection" + getStackTrace()); //CTEST
    }

    public static boolean reportUnconfirmedRepairedDataMismatches()
    {
        logger.warn("[CTEST][GET-PARAM] " + "report_unconfirmed_repaired_data_mismatches" ); //CTEST
        return conf.report_unconfirmed_repaired_data_mismatches;
    }

    public static void reportUnconfirmedRepairedDataMismatches(boolean enabled)
    {
        conf.report_unconfirmed_repaired_data_mismatches = enabled;
        logger.warn("[CTEST][SET-PARAM] " + "report_unconfirmed_repaired_data_mismatches" + getStackTrace()); //CTEST
    }

    public static boolean strictRuntimeChecks()
    {
        return strictRuntimeChecks;
    }

    public static boolean useOffheapMerkleTrees()
    {
        logger.warn("[CTEST][GET-PARAM] " + "use_offheap_merkle_trees" ); //CTEST
        return conf.use_offheap_merkle_trees;
    }

    public static void useOffheapMerkleTrees(boolean value)
    {
        logger.info("Setting use_offheap_merkle_trees to {}", value);
        conf.use_offheap_merkle_trees = value;
        logger.warn("[CTEST][SET-PARAM] " + "use_offheap_merkle_trees" + getStackTrace()); //CTEST
    }

    public static Function<CommitLog, AbstractCommitLogSegmentManager> getCommitLogSegmentMgrProvider()
    {
        return commitLogSegmentMgrProvider;
    }

    public static void setCommitLogSegmentMgrProvider(Function<CommitLog, AbstractCommitLogSegmentManager> provider)
    {
        commitLogSegmentMgrProvider = provider;
    }

    /**
     * Class that primarily tracks overflow thresholds during conversions
     */
    private enum ByteUnit {
        KIBI_BYTES(2048 * 1024, 1024),
        MEBI_BYTES(2048, 1024 * 1024);

        private final int overflowThreshold;
        private final int multiplier;

        ByteUnit(int t, int m)
        {
            this.overflowThreshold = t;
            this.multiplier = m;
        }

        public int overflowThreshold()
        {
            return overflowThreshold;
        }

        public boolean willOverflowInBytes(int val)
        {
            return val >= overflowThreshold;
        }

        public long toBytes(int val)
        {
            return val * multiplier;
        }
    }

    /**
     * Ensures passed in configuration value is positive and will not overflow when converted to Bytes
     */
    private static void checkValidForByteConversion(int val, final String name, final ByteUnit unit)
    {
        if (val < 0 || unit.willOverflowInBytes(val))
            throw new ConfigurationException(String.format("%s must be positive value < %d, but was %d",
                                                           name, unit.overflowThreshold(), val), false);
    }

    public static int getValidationPreviewPurgeHeadStartInSec()
    {
        logger.warn("[CTEST][GET-PARAM] " + "validation_preview_purge_head_start_in_sec" ); //CTEST
        int seconds = conf.validation_preview_purge_head_start_in_sec;
        return Math.max(seconds, 0);
    }

    public static boolean checkForDuplicateRowsDuringReads()
    {
        logger.warn("[CTEST][GET-PARAM] " + "check_for_duplicate_rows_during_reads" ); //CTEST
        return conf.check_for_duplicate_rows_during_reads;
    }

    public static void setCheckForDuplicateRowsDuringReads(boolean enabled)
    {
        conf.check_for_duplicate_rows_during_reads = enabled;
        logger.warn("[CTEST][SET-PARAM] " + "check_for_duplicate_rows_during_reads" + getStackTrace()); //CTEST
    }

    public static boolean checkForDuplicateRowsDuringCompaction()
    {
        logger.warn("[CTEST][GET-PARAM] " + "check_for_duplicate_rows_during_compaction" ); //CTEST
        return conf.check_for_duplicate_rows_during_compaction;
    }

    public static void setCheckForDuplicateRowsDuringCompaction(boolean enabled)
    {
        conf.check_for_duplicate_rows_during_compaction = enabled;
        logger.warn("[CTEST][SET-PARAM] " + "check_for_duplicate_rows_during_compaction" + getStackTrace()); //CTEST
    }

    public static int getRepairPendingCompactionRejectThreshold()
    {
        logger.warn("[CTEST][GET-PARAM] " + "reject_repair_compaction_threshold" ); //CTEST
        return conf.reject_repair_compaction_threshold;
    }

    public static void setRepairPendingCompactionRejectThreshold(int value)
    {
        conf.reject_repair_compaction_threshold = value;
        logger.warn("[CTEST][SET-PARAM] " + "reject_repair_compaction_threshold" + getStackTrace()); //CTEST
    }

    public static int getInitialRangeTombstoneListAllocationSize()
    {
        logger.warn("[CTEST][GET-PARAM] " + "initial_range_tombstone_list_allocation_size" ); //CTEST
        return conf.initial_range_tombstone_list_allocation_size;
    }

    public static void setInitialRangeTombstoneListAllocationSize(int size)
    {
        conf.initial_range_tombstone_list_allocation_size = size;
        logger.warn("[CTEST][SET-PARAM] " + "initial_range_tombstone_list_allocation_size" + getStackTrace()); //CTEST
    }

    public static double getRangeTombstoneListGrowthFactor()
    {
        logger.warn("[CTEST][GET-PARAM] " + "range_tombstone_list_growth_factor" ); //CTEST
        return conf.range_tombstone_list_growth_factor;
    }

    public static void setRangeTombstoneListGrowthFactor(double resizeFactor)
    {
        conf.range_tombstone_list_growth_factor = resizeFactor;
        logger.warn("[CTEST][SET-PARAM] " + "range_tombstone_list_growth_factor" + getStackTrace()); //CTEST
    }

    public static boolean getAutocompactionOnStartupEnabled()
    {
        logger.warn("[CTEST][GET-PARAM] " + "autocompaction_on_startup_enabled" ); //CTEST
        return conf.autocompaction_on_startup_enabled;
    }

    public static boolean autoOptimiseIncRepairStreams()
    {
        logger.warn("[CTEST][GET-PARAM] " + "auto_optimise_inc_repair_streams" ); //CTEST
        return conf.auto_optimise_inc_repair_streams;
    }

    public static void setAutoOptimiseIncRepairStreams(boolean enabled)
    {
        if (enabled != conf.auto_optimise_inc_repair_streams)
            logger.info("Changing auto_optimise_inc_repair_streams from {} to {}", conf.auto_optimise_inc_repair_streams, enabled);
        conf.auto_optimise_inc_repair_streams = enabled;
        logger.warn("[CTEST][SET-PARAM] " + "auto_optimise_inc_repair_streams" + getStackTrace()); //CTEST
    }

    public static boolean autoOptimiseFullRepairStreams()
    {
        logger.warn("[CTEST][GET-PARAM] " + "auto_optimise_full_repair_streams" ); //CTEST
        return conf.auto_optimise_full_repair_streams;
    }

    public static void setAutoOptimiseFullRepairStreams(boolean enabled)
    {
        if (enabled != conf.auto_optimise_full_repair_streams)
            logger.info("Changing auto_optimise_full_repair_streams from {} to {}", conf.auto_optimise_full_repair_streams, enabled);
        conf.auto_optimise_full_repair_streams = enabled;
        logger.warn("[CTEST][SET-PARAM] " + "auto_optimise_full_repair_streams" + getStackTrace()); //CTEST
    }

    public static boolean autoOptimisePreviewRepairStreams()
    {
        logger.warn("[CTEST][GET-PARAM] " + "auto_optimise_preview_repair_streams" ); //CTEST
        return conf.auto_optimise_preview_repair_streams;
    }

    public static void setAutoOptimisePreviewRepairStreams(boolean enabled)
    {
        if (enabled != conf.auto_optimise_preview_repair_streams)
            logger.info("Changing auto_optimise_preview_repair_streams from {} to {}", conf.auto_optimise_preview_repair_streams, enabled);
        conf.auto_optimise_preview_repair_streams = enabled;
        logger.warn("[CTEST][SET-PARAM] " + "auto_optimise_preview_repair_streams" + getStackTrace()); //CTEST
    }

    public static int tableCountWarnThreshold()
    {
        logger.warn("[CTEST][GET-PARAM] " + "table_count_warn_threshold" ); //CTEST
        return conf.table_count_warn_threshold;
    }

    public static void setTableCountWarnThreshold(int value)
    {
        conf.table_count_warn_threshold = value;
        logger.warn("[CTEST][SET-PARAM] " + "table_count_warn_threshold" + getStackTrace()); //CTEST
    }

    public static int keyspaceCountWarnThreshold()
    {
        logger.warn("[CTEST][GET-PARAM] " + "keyspace_count_warn_threshold" ); //CTEST
        return conf.keyspace_count_warn_threshold;
    }

    public static void setKeyspaceCountWarnThreshold(int value)
    {
        conf.keyspace_count_warn_threshold = value;
        logger.warn("[CTEST][SET-PARAM] " + "keyspace_count_warn_threshold" + getStackTrace()); //CTEST
    }

    public static int getConsecutiveMessageErrorsThreshold()
    {
        logger.warn("[CTEST][GET-PARAM] " + "consecutive_message_errors_threshold" ); //CTEST
        return conf.consecutive_message_errors_threshold;
    }

    public static void setConsecutiveMessageErrorsThreshold(int value)
    {
        conf.consecutive_message_errors_threshold = value;
        logger.warn("[CTEST][SET-PARAM] " + "consecutive_message_errors_threshold" + getStackTrace()); //CTEST
    }

    public static boolean getForceNewPreparedStatementBehaviour()
    {
        logger.warn("[CTEST][GET-PARAM] " + "force_new_prepared_statement_behaviour" ); //CTEST
        return conf.force_new_prepared_statement_behaviour;
    }

    public static void setForceNewPreparedStatementBehaviour(boolean value)
    {
        if (value != conf.force_new_prepared_statement_behaviour)
        {
            logger.info("Setting force_new_prepared_statement_behaviour to {}", value);
            conf.force_new_prepared_statement_behaviour = value;
            logger.warn("[CTEST][SET-PARAM] " + "force_new_prepared_statement_behaviour" + getStackTrace()); //CTEST
        }
    }

    // CTEST
    private static String getStackTrace() {
        String stacktrace = " ";
        for (StackTraceElement element : Thread.currentThread().getStackTrace()) {
            stacktrace = stacktrace.concat(
                element.getClassName() + "#" + element.getMethodName() + "#" + element.getLineNumber() + "\t"
            );
        }
        return stacktrace;
    }
}
