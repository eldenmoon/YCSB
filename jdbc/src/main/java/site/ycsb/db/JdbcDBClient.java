/**
 * Copyright (c) 2010 - 2016 Yahoo! Inc., 2016, 2019 YCSB contributors. All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License"); you
 * may not use this file except in compliance with the License. You
 * may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
 * implied. See the License for the specific language governing
 * permissions and limitations under the License. See accompanying
 * LICENSE file.
 */
package site.ycsb.db;

import site.ycsb.DB;
import site.ycsb.DBException;
import site.ycsb.ByteIterator;
import site.ycsb.Status;
import site.ycsb.StringByteIterator;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.sql.*;
import java.util.*;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ConcurrentMap;
import java.util.concurrent.atomic.AtomicInteger;

import org.apache.commons.codec.binary.Base64;
import org.apache.http.HttpHeaders;
import org.apache.http.client.methods.CloseableHttpResponse;
import org.apache.http.client.methods.HttpPut;
import org.apache.http.entity.StringEntity;
import org.apache.http.impl.client.CloseableHttpClient;
import org.apache.http.impl.client.DefaultRedirectStrategy;
import org.apache.http.impl.client.HttpClientBuilder;
import org.apache.http.impl.client.HttpClients;
import org.apache.http.util.EntityUtils;

import com.fasterxml.jackson.core.JsonProcessingException;
import com.fasterxml.jackson.databind.ObjectMapper;

import site.ycsb.db.flavors.DBFlavor;

/**
 * A class that wraps a JDBC compliant database to allow it to be interfaced
 * with YCSB. This class extends {@link DB} and implements the database
 * interface used by YCSB client.
 *
 * <br>
 * Each client will have its own instance of this class. This client is not
 * thread safe.
 *
 * <br>
 * This interface expects a schema <key> <field1> <field2> <field3> ... All
 * attributes are of type TEXT. All accesses are through the primary key.
 * Therefore, only one index on the primary key is needed.
 */
public class JdbcDBClient extends DB {

  /** The class to use as the jdbc driver. */
  public static final String DRIVER_CLASS = "db.driver";

  /** The URL to connect to the database. */
  public static final String CONNECTION_URL = "db.url";

  /** The user name to use to connect to the database. */
  public static final String CONNECTION_USER = "db.user";

  /** The password to use for establishing the connection. */
  public static final String CONNECTION_PASSWD = "db.passwd";

  /** The password to use for establishing the connection. */
  public static final String DORIS_LOAD_URL = "doris.load_url";

  /** The batch size for batched inserts. Set to >0 to use batching */
  public static final String DB_BATCH_SIZE = "db.batchsize";

  /** The JDBC fetch size hinted to the driver. */
  public static final String JDBC_FETCH_SIZE = "jdbc.fetchsize";

  /** The JDBC connection auto-commit property for the driver. */
  public static final String JDBC_AUTO_COMMIT = "jdbc.autocommit";

  public static final String JDBC_BATCH_UPDATES = "jdbc.batchupdateapi";

  /** The name of the property for the number of fields in a record. */
  public static final String FIELD_COUNT_PROPERTY = "fieldcount";

  /** Default number of fields in a record. */
  public static final String FIELD_COUNT_PROPERTY_DEFAULT = "10";

  /** Representing a NULL value. */
  public static final String NULL_VALUE = "NULL";

  /** The primary key in the user table. */
  public static String PRIMARY_KEY = "YCSB_KEY";
  private Map<String, String> columnValue = new HashMap<String, String>();
  public static int KEY_LEN = 100;
  public static String USER_TABLE = "";

  /** The field name prefix in the table. */
  public static final String COLUMN_PREFIX = "FIELD";

  /** SQL:2008 standard: FETCH FIRST n ROWS after the ORDER BY. */
  private boolean sqlansiScans = false;
  /** SQL Server before 2012: TOP n after the SELECT. */
  private boolean sqlserverScans = false;

  private boolean readPrepared = false;
  private long curBatchSize = 0;

  private List<Connection> conns;
  private List<Boolean> connsPrepared;
  private boolean initialized = false;
  private Properties props;
  private int jdbcFetchSize;
  private int batchSize;
  private boolean autoCommit;
  private boolean batchUpdates;
  private static final String DEFAULT_PROP = "";
  private ConcurrentMap<StatementType, PreparedStatement> cachedStatements;
  private long numRowsInBatch = 0;
  private String user;
  private String passwd;
  private String loadURL;
  private StringBuilder bufferString = new StringBuilder();
  /** DB flavor defines DB-specific syntax and behavior for the
   * particular database. Current database flavors are: {default, phoenix} */
  private DBFlavor dbFlavor;

  // custom config
  private int columnSize = 20;
  private int columnCount = 20;
  private boolean vacummTable = false;
  private boolean runCustomMode = true;
  private boolean isInQuery = false;
  private int inListSize = 10;
  private long recordCount = 10000000;
  private static AtomicInteger currentRecord = new AtomicInteger(0);

  Random random = new Random();

  /**
   * Ordered field information for insert and update statements.
   */
  private static class OrderedFieldInfo {
    private String fieldKeys;
    private List<String> fieldValues;

    OrderedFieldInfo(String fieldKeys, List<String> fieldValues) {
      this.fieldKeys = fieldKeys;
      this.fieldValues = fieldValues;
    }

    String getFieldKeys() {
      return fieldKeys;
    }

    List<String> getFieldValues() {
      return fieldValues;
    }
  }

  /**
   * For the given key, returns what shard contains data for this key.
   *
   * @param key Data key to do operation on
   * @return Shard index
   */
  private int getShardIndexByKey(String key) {
    int ret = Math.abs(key.hashCode()) % conns.size();
    return ret;
  }

  /**
   * For the given key, returns Connection object that holds connection to the
   * shard that contains this key.
   *
   * @param key Data key to get information for
   * @return Connection object
   */
  private Connection getShardConnectionByKey(String key) {
    return conns.get(getShardIndexByKey(key));
  }

  private void cleanupAllConnections() throws SQLException {
    for (Connection conn : conns) {
      if (!autoCommit) {
        conn.commit();
      }
      conn.close();
    }
  }

  /** Returns parsed int value from the properties if set, otherwise returns -1. */
  private static int getIntProperty(Properties props, String key) throws DBException {
    String valueStr = props.getProperty(key);
    if (valueStr != null) {
      try {
        return Integer.parseInt(valueStr);
      } catch (NumberFormatException nfe) {
        System.err.println("Invalid " + key + " specified: " + valueStr);
        throw new DBException(nfe);
      }
    }
    return -1;
  }

  /** Returns parsed boolean value from the properties if set, otherwise returns defaultVal. */
  private static boolean getBoolProperty(Properties props, String key, boolean defaultVal) {
    String valueStr = props.getProperty(key);
    if (valueStr != null) {
      return Boolean.parseBoolean(valueStr);
    }
    return defaultVal;
  }

  public void customInit() throws DBException {
    // Use BigInt as primary key
    PRIMARY_KEY = "customer_key";
    USER_TABLE = "customer";
    // SQL for create table
    String createTableSql = "CREATE TABLE IF NOT EXISTS " + USER_TABLE + "\n";
    createTableSql += "(" + PRIMARY_KEY + " BIGINT,\n";
    for (int i = 0; i < columnCount - 1; ++i) {
      createTableSql += USER_TABLE + "_value_" + i + " STRING,\n";
    }
    createTableSql += USER_TABLE + "_value_" + columnCount + " STRING)\n";
    createTableSql += "UNIQUE KEY(" + PRIMARY_KEY + ")\n";
    createTableSql += "DISTRIBUTED BY HASH(" + PRIMARY_KEY + ")\n";
    createTableSql += "PROPERTIES(\"replication_num\"=\"1\",\"store_row_column\"=\"true\", \"enable_unique_key_merge_on_write\"=\"true\")\n";
    System.out.println("create table sql :" + createTableSql);

    try {
      Connection conn = getShardConnectionByKey("connection");
      Statement createTableStmt = conn.createStatement(); 
      createTableStmt.execute(createTableSql); 
      if (vacummTable) {
        Statement vacTableStmt = conn.createStatement(); 
        vacTableStmt.execute("TRUNCATE TABLE " + USER_TABLE);
      }
    } catch (SQLException e) {
      throw new DBException("error when create table: " + e);
    }
  }

  @Override
  public void init() throws DBException {
    if (initialized) {
      System.err.println("Client connection already initialized.");
      return;
    }
    props = getProperties();
    String urls = props.getProperty(CONNECTION_URL, DEFAULT_PROP);
    String driver = props.getProperty(DRIVER_CLASS);
    PRIMARY_KEY = props.getProperty("db.keyName", PRIMARY_KEY);
    USER_TABLE = props.getProperty("db.tableName", USER_TABLE);

    user = props.getProperty(CONNECTION_USER, DEFAULT_PROP);
    passwd = props.getProperty(CONNECTION_PASSWD, DEFAULT_PROP);
    loadURL = props.getProperty(DORIS_LOAD_URL, "");

    this.jdbcFetchSize = getIntProperty(props, JDBC_FETCH_SIZE);
    this.batchSize = getIntProperty(props, DB_BATCH_SIZE);

    this.autoCommit = getBoolProperty(props, JDBC_AUTO_COMMIT, true);
    this.batchUpdates = getBoolProperty(props, JDBC_BATCH_UPDATES, false);

    // custom configs
    this.runCustomMode = getBoolProperty(props, "db.runCustomMode", false);
    this.isInQuery = getBoolProperty(props, "db.isInQuery", false);
    this.inListSize = getIntProperty(props, "db.inListSize");
    this.columnCount = getIntProperty(props, "db.columnCount");
    if (this.columnCount <= 0) {
      this.columnCount = 20;
    }
    this.columnSize = getIntProperty(props, "db.columnSize");
    if (this.columnSize <= 0) {
      this.columnSize = 20;
    }
    this.vacummTable = getBoolProperty(props, "db.vacummTable", false);
    this.recordCount = getIntProperty(props, "db.recordCount");
    if (this.recordCount <= 0) {
      this.recordCount = 10000000;
    }

    try {
//  The SQL Syntax for Scan depends on the DB engine
//  - SQL:2008 standard: FETCH FIRST n ROWS after the ORDER BY
//  - SQL Server before 2012: TOP n after the SELECT
//  - others (MySQL,MariaDB, PostgreSQL before 8.4)
//  TODO: check product name and version rather than driver name
      if (driver != null) {
        if (driver.contains("sqlserver")) {
          sqlserverScans = true;
          sqlansiScans = false;
        }
        if (driver.contains("oracle")) {
          sqlserverScans = false;
          sqlansiScans = true;
        }
        if (driver.contains("postgres")) {
          sqlserverScans = false;
          sqlansiScans = true;
        }
        Class.forName(driver);
      }
      int shardCount = 0;
      conns = new ArrayList<Connection>(3);
      connsPrepared = new ArrayList<>();
      // for a longer explanation see the README.md
      // semicolons aren't present in JDBC urls, so we use them to delimit
      // multiple JDBC connections to shard across.
      final String[] urlArr = urls.split(";");
      for (String url : urlArr) {
        System.out.println("Adding shard node URL: " + url);
        Connection conn = DriverManager.getConnection(url, user, passwd);

        // Since there is no explicit commit method in the DB interface, all
        // operations should auto commit, except when explicitly told not to
        // (this is necessary in cases such as for PostgreSQL when running a
        // scan workload with fetchSize)
        conn.setAutoCommit(autoCommit);

        shardCount++;
        conns.add(conn);
        connsPrepared.add(false);
      }

      System.out.println("Using shards: " + shardCount + ", batchSize:" + batchSize + ", fetchSize: " + jdbcFetchSize);

      cachedStatements = new ConcurrentHashMap<StatementType, PreparedStatement>();

      this.dbFlavor = DBFlavor.fromJdbcUrl(urlArr[0]);
    } catch (ClassNotFoundException e) {
      System.err.println("Error in initializing the JDBS driver: " + e);
      throw new DBException(e);
    } catch (SQLException e) {
      System.err.println("Error in database operation: " + e);
      throw new DBException(e);
    } catch (NumberFormatException e) {
      System.err.println("Invalid value for fieldcount property. " + e);
      throw new DBException(e);
    }

    if (runCustomMode) {
      customInit(); 
    }

    initialized = true;
  }

  @Override
  public void cleanup() throws DBException {
    if (batchSize > 0) {
      try {
        // commit un-finished batches
        for (PreparedStatement st : cachedStatements.values()) {
          if (!st.getConnection().isClosed() && !st.isClosed() && (numRowsInBatch % batchSize != 0)) {
            st.executeBatch();
          }
        }
      } catch (SQLException e) {
        System.err.println("Error in cleanup execution. " + e);
        throw new DBException(e);
      }
    }

    try {
      cleanupAllConnections();
    } catch (SQLException e) {
      System.err.println("Error in closing the connection. " + e);
      throw new DBException(e);
    }
  }

  private PreparedStatement createAndCacheInsertStatement(StatementType insertType, String key)
      throws SQLException {
    String insert = dbFlavor.createInsertStatement(insertType, key);
    PreparedStatement insertStatement = getShardConnectionByKey(key).prepareStatement(insert);
    PreparedStatement stmt = cachedStatements.putIfAbsent(insertType, insertStatement);
    if (stmt == null) {
      return insertStatement;
    }
    return stmt;
  }

  private PreparedStatement createAndCacheReadStatement(StatementType readType, String key)
      throws SQLException {
    String read = dbFlavor.createReadStatement(readType, key);
    PreparedStatement readStatement = getShardConnectionByKey(key).prepareStatement(read);
    PreparedStatement stmt = cachedStatements.putIfAbsent(readType, readStatement);
    if (stmt == null) {
      return readStatement;
    }
    return stmt;
  }

  private PreparedStatement createAndCacheBatchReadStatement(StatementType readType, String key, int inBatchSize)
    throws SQLException {
    String read = dbFlavor.createBatchReadStatement(readType, key, inBatchSize);
    // todo: not sure if this is correct
    PreparedStatement readStatement = getShardConnectionByKey(key).prepareStatement(read);
    PreparedStatement stmt = cachedStatements.putIfAbsent(readType, readStatement);
    if (stmt == null) {
      return readStatement;
    }
    return stmt;
  }

  private PreparedStatement createAndCacheExecuteStatement(StatementType readType, String key)
      throws SQLException {
    String read = dbFlavor.createExecuteStatement();
    PreparedStatement readStatement = getShardConnectionByKey(key).prepareStatement(read);
    PreparedStatement stmt = cachedStatements.putIfAbsent(readType, readStatement);
    if (stmt == null) {
      return readStatement;
    }
    return stmt;
  }

  private PreparedStatement createAndCacheDeleteStatement(StatementType deleteType, String key)
      throws SQLException {
    String delete = dbFlavor.createDeleteStatement(deleteType, key);
    PreparedStatement deleteStatement = getShardConnectionByKey(key).prepareStatement(delete);
    PreparedStatement stmt = cachedStatements.putIfAbsent(deleteType, deleteStatement);
    if (stmt == null) {
      return deleteStatement;
    }
    return stmt;
  }

  private PreparedStatement createAndCacheUpdateStatement(StatementType updateType, String key)
      throws SQLException {
    String update = dbFlavor.createUpdateStatement(updateType, key);
    PreparedStatement insertStatement = getShardConnectionByKey(key).prepareStatement(update);
    PreparedStatement stmt = cachedStatements.putIfAbsent(updateType, insertStatement);
    if (stmt == null) {
      return insertStatement;
    }
    return stmt;
  }

  private PreparedStatement createAndCacheScanStatement(StatementType scanType, String key)
      throws SQLException {
    String select = dbFlavor.createScanStatement(scanType, key, sqlserverScans, sqlansiScans);
    PreparedStatement scanStatement = getShardConnectionByKey(key).prepareStatement(select);
    if (this.jdbcFetchSize > 0) {
      scanStatement.setFetchSize(this.jdbcFetchSize);
    }
    PreparedStatement stmt = cachedStatements.putIfAbsent(scanType, scanStatement);
    if (stmt == null) {
      return scanStatement;
    }
    return stmt;
  }

  @Override
  public Status read(String tableName, String key, Set<String> fields, Map<String, ByteIterator> result) {
    try {
      if (!USER_TABLE.isEmpty()) {
        tableName = USER_TABLE;
      }
      PreparedStatement readStatement = null;
      if (runCustomMode || !USER_TABLE.isEmpty()) {
        long rankey;
        String newKey = "";
        if (isInQuery) {
          List<Long> newKeysLong = new ArrayList<Long>();
          List<String> newKeysString = new ArrayList<String>();
          for (int i = 0; i < inListSize; ++i) {
            rankey = random.nextInt((int) recordCount);
            newKey = String.valueOf(rankey);
            newKeysLong.add(rankey);
            newKeysString.add(newKey);
          }
          StatementType type = new StatementType(StatementType.Type.READ, tableName, 1, "", getShardIndexByKey(newKeysString.get(0))); 
          readStatement = cachedStatements.get(type);
          if (readStatement == null) {
            readStatement = createAndCacheBatchReadStatement(type, newKeysString.get(0), inListSize);
          }
          for (int i = 0; i < inListSize; ++i) {
            readStatement.setLong(i + 1, newKeysLong.get(i));
          }
        } else {
          rankey = random.nextInt((int) recordCount);
          newKey = String.valueOf(rankey);
          StatementType type = new StatementType(StatementType.Type.READ, tableName, 1, "", getShardIndexByKey(newKey)); 
          readStatement = cachedStatements.get(type);
          if (readStatement == null) {
            readStatement = createAndCacheReadStatement(type, newKey);
          }
          readStatement.setLong(1, rankey);
        }
      } else {
        key = key.substring(0, KEY_LEN);
        StatementType type = new StatementType(StatementType.Type.READ, tableName, 1, "", getShardIndexByKey(key));
        readStatement = cachedStatements.get(type);
        if (readStatement == null) {
          readStatement = createAndCacheReadStatement(type, key);
        }
        readStatement.setString(1, key);
      }
      ResultSet resultSet = readStatement.executeQuery();
      if (!resultSet.next()) {
        resultSet.close();
        return Status.NOT_FOUND;
      }
      if (result != null && fields != null) {
        for (String field : fields) {
          String value = resultSet.getString(field);
          result.put(field, new StringByteIterator(value));
        }
      }
      resultSet.close();
      return Status.OK;
    } catch (SQLException e) {
      System.err.println("Error in processing read of table " + tableName + ": " + e);
      return Status.ERROR;
    }
  }

  @Override
  public Status scan(String tableName, String startKey, int recordcount, Set<String> fields,
                     Vector<HashMap<String, ByteIterator>> result) {
    try {
      StatementType type = new StatementType(StatementType.Type.SCAN, tableName, 1, "", getShardIndexByKey(startKey));
      PreparedStatement scanStatement = cachedStatements.get(type);
      if (scanStatement == null) {
        scanStatement = createAndCacheScanStatement(type, startKey);
      }
      // SQL Server TOP syntax is at first
      if (sqlserverScans) {
        scanStatement.setInt(1, recordcount);
        scanStatement.setString(2, startKey);
      // FETCH FIRST and LIMIT are at the end
      } else {
        scanStatement.setString(1, startKey);
        scanStatement.setInt(2, recordcount);
      }
      ResultSet resultSet = scanStatement.executeQuery();
      for (int i = 0; i < recordcount && resultSet.next(); i++) {
        if (result != null && fields != null) {
          HashMap<String, ByteIterator> values = new HashMap<String, ByteIterator>();
          for (String field : fields) {
            String value = resultSet.getString(field);
            values.put(field, new StringByteIterator(value));
          }
          result.add(values);
        }
      }
      resultSet.close();
      return Status.OK;
    } catch (SQLException e) {
      System.err.println("Error in processing scan of table: " + tableName + e);
      return Status.ERROR;
    }
  }

  @Override
  public Status update(String tableName, String key, Map<String, ByteIterator> values) {
    try {
      int numFields = values.size();
      OrderedFieldInfo fieldInfo = getFieldInfo(values);
      StatementType type = new StatementType(StatementType.Type.UPDATE, tableName,
          numFields, fieldInfo.getFieldKeys(), getShardIndexByKey(key));
      PreparedStatement updateStatement = cachedStatements.get(type);
      if (updateStatement == null) {
        updateStatement = createAndCacheUpdateStatement(type, key);
      }
      int index = 1;
      for (String value: fieldInfo.getFieldValues()) {
        updateStatement.setString(index++, value);
      }
      updateStatement.setString(index, key);
      int result = updateStatement.executeUpdate();
      if (result == 1) {
        return Status.OK;
      }
      return Status.UNEXPECTED_STATE;
    } catch (SQLException e) {
      System.err.println("Error in processing update to table: " + tableName + e);
      return Status.ERROR;
    }
  }

  private String genRandomString(int length) {
    // set of characters to use in generating the string
    String characters = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789";
        
    StringBuilder sb = new StringBuilder(length);
    // generate random characters and append to string builder
    for (int i = 0; i < length - 1; i++) {
      int randomIndex = random.nextInt(characters.length());
      char randomChar = characters.charAt(randomIndex);
      sb.append(randomChar);
    }
        
    return sb.toString();  
  }

  private Status insertWithStatement(String tableName, String key,
                  OrderedFieldInfo fieldInfo, boolean isCustomTable) {
    try {
      PreparedStatement insertStatement = null;
      if (isCustomTable) {
        // Generate random primary key and value
        if (currentRecord.get() > recordCount) {
          return Status.OK;
        }
        int numFields = columnCount;
        // List<String> fields = new ArrayList<String>();
        StatementType type = new StatementType(StatementType.Type.INSERT, tableName,
            numFields, "", getShardIndexByKey(String.valueOf(currentRecord.get())));
        insertStatement = cachedStatements.get(type);
        if (insertStatement == null) {
          insertStatement = createAndCacheInsertStatement(type, String.valueOf(currentRecord.get()));
        } 
        // key
        synchronized (this) {
          insertStatement.setInt(1, (int) currentRecord.getAndIncrement());
        }
        int index = 2;
        for (int i = 0; i < columnCount; ++i) {
          insertStatement.setString(i+index, genRandomString(columnSize));
        }
      } else {
        int numFields = fieldInfo.getFieldValues().size();
        StatementType type = new StatementType(StatementType.Type.INSERT, tableName,
            numFields, fieldInfo.getFieldKeys(), getShardIndexByKey(key));
        insertStatement = cachedStatements.get(type);
        if (insertStatement == null) {
          insertStatement = createAndCacheInsertStatement(type, key);
        }
        insertStatement.setString(1, key);
        int index = 2;
        for (String value: fieldInfo.getFieldValues()) {
          insertStatement.setString(index++, value);
        }
      }
      // Using the batch insert API
      if (batchUpdates) {
        insertStatement.addBatch();
        // Check for a sane batch size
        if (batchSize > 0) {
          // Commit the batch after it grows beyond the configured size
          if (++numRowsInBatch % batchSize == 0) {
            int[] results = insertStatement.executeBatch();
            for (int r : results) {
              // Acceptable values are 1 and SUCCESS_NO_INFO (-2) from reWriteBatchedInserts=true
              if (r != 1 && r != -2) { 
                return Status.ERROR;
              }
            }
            // If autoCommit is off, make sure we commit the batch
            if (!autoCommit) {
              getShardConnectionByKey(key).commit();
            }
            return Status.OK;
          } // else, the default value of -1 or a nonsense. Treat it as an infinitely large batch.
        } // else, we let the batch accumulate
        // Added element to the batch, potentially committing the batch too.
        return Status.BATCHED_OK;
      } else {
        // Normal update
        int result = insertStatement.executeUpdate();
        // If we are not autoCommit, we might have to commit now
        if (!autoCommit) {
          // Let updates be batcher locally
          if (batchSize > 0) {
            if (++numRowsInBatch % batchSize == 0) {
              // Send the batch of updates
              getShardConnectionByKey(key).commit();
            }
            // uhh
            return Status.OK;
          } else {
            // Commit each update
            getShardConnectionByKey(key).commit();
          }
        }
        if (result == 1) {
          return Status.OK;
        }
      }
      return Status.UNEXPECTED_STATE;
    } catch (SQLException e) {
      System.err.println("Error in processing insert to table: " + tableName + e);
      return Status.ERROR;
    }
  }
  
  private Status insertWithStatement(String tableName,
                  String key, Map<String, ByteIterator> values) {
    return insertWithStatement(tableName, key, getFieldInfo(values), false);
  }

  @Override
  public Status insert(String tableName, String key, Map<String, ByteIterator> values) {
    int numFields = values.size();
    Map<String, String> map = new HashMap<>(); 
    if (runCustomMode) {
      // Generate random primary key and value to json streamLoad
      if (currentRecord.get() > recordCount) {
        return Status.OK;
      }
      // key
      map.put(PRIMARY_KEY, String.valueOf(currentRecord.getAndIncrement()));
      // value
      for (int i = 0; i < columnCount; ++i) {
        map.put(USER_TABLE + "_value_" + i, genRandomString(columnSize));
      }
      // Create an ObjectMapper
      ObjectMapper mapper = new ObjectMapper();
      String json = null;
      try {
        // Convert the map to a JSON string
        json = mapper.writeValueAsString(map);
      } catch (JsonProcessingException e) {
        e.printStackTrace();
      }
      return dorisStreamLoad(json);
    } else {
      // map.put(PRIMARY_KEY, key.substring(0, KEY_LEN));
      // for (Map.Entry<String, ByteIterator> entry : values.entrySet()) {
      //   map.put(entry.getKey().toUpperCase(), entry.getValue().toString());
      // }
      if (!USER_TABLE.isEmpty()) {
        // USER table
        tableName = USER_TABLE;
        return insertWithStatement(tableName, null, null, true);
      }
      // YCSB table
      return insertWithStatement(tableName, key, values);
    }
  }

  private String basicAuthHeader(String username, String password) {
    final String tobeEncode = username + ":" + password;
    byte[] encoded = Base64.encodeBase64(tobeEncode.getBytes(StandardCharsets.UTF_8));
    return "Basic " + new String(encoded);
  }

  public Status dorisStreamLoad(String valueJson) {
    bufferString.append(valueJson);
    bufferString.append("\n");
    if (++numRowsInBatch % batchSize != 0) {
      // uhh
      return Status.OK;
    }
    // Send the batch of updates
    String buff;
    buff = bufferString.toString();
    bufferString = new StringBuilder();
    HttpClientBuilder httpClientBuilder = HttpClients
            .custom()
            .setRedirectStrategy(new DefaultRedirectStrategy() {
                @Override
                protected boolean isRedirectable(String method) {
                    // If the connection target is FE, you need to handle 307 redirect.
                    return true;
                }
            });

    try (CloseableHttpClient client = httpClientBuilder.build()) {
      HttpPut put = new HttpPut(loadURL);
      // put.setHeader(HttpHeaders.EXPECT, "100-continue");
      // put.setHeader(HttpHeaders.AUTHORIZATION, basicAuthHeader(user, passwd));
      put.setHeader("read_json_by_line", "true");
      put.setHeader("format", "json");
      put.setHeader("expect", "100-continue");
      put.setHeader(HttpHeaders.AUTHORIZATION, basicAuthHeader(user, passwd));
      StringEntity buffEntity = new StringEntity(buff);
      // StringEntity can also be used here to transfer arbitrary data.
      put.setEntity(buffEntity);
      try (CloseableHttpResponse response = client.execute(put)) {
        String loadResult = "";
        if (response.getEntity() != null) {
          loadResult = EntityUtils.toString(response.getEntity());
        }

        final int statusCode = response.getStatusLine().getStatusCode();
        if (statusCode != 200) {
          throw new IOException(
                    String.format("Stream load failed. status: %s load result: %s", statusCode, loadResult));
        }
        System.out.println("Get load result: " + loadResult);
      } catch (IOException e) {
        e.printStackTrace();
        return Status.ERROR;
      }
    } catch (IOException e) {
      e.printStackTrace();
      return Status.ERROR;
    }
    return Status.OK;
  }

  @Override
  public Status delete(String tableName, String key) {
    try {
      StatementType type = new StatementType(StatementType.Type.DELETE, tableName, 1, "", getShardIndexByKey(key));
      PreparedStatement deleteStatement = cachedStatements.get(type);
      if (deleteStatement == null) {
        deleteStatement = createAndCacheDeleteStatement(type, key);
      }
      deleteStatement.setString(1, key);
      int result = deleteStatement.executeUpdate();
      if (result == 1) {
        return Status.OK;
      }
      return Status.UNEXPECTED_STATE;
    } catch (SQLException e) {
      System.err.println("Error in processing delete to table: " + tableName + e);
      return Status.ERROR;
    }
  }

  private OrderedFieldInfo getFieldInfo(Map<String, ByteIterator> values) {
    String fieldKeys = "";
    List<String> fieldValues = new ArrayList<>();
    int count = 0;
    for (Map.Entry<String, ByteIterator> entry : values.entrySet()) {
      fieldKeys += entry.getKey();
      if (count < values.size() - 1) {
        fieldKeys += ",";
      }
      fieldValues.add(count, entry.getValue().toString());
      count++;
    }

    return new OrderedFieldInfo(fieldKeys, fieldValues);
  }
}
