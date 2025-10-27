package utils;

import org.apache.tomcat.jdbc.pool.DataSource;
import org.apache.tomcat.jdbc.pool.PoolProperties;

import java.sql.Connection;
import java.sql.SQLException;

public class ConPool {
    private static DataSource datasource;

    public static Connection getConnection() throws SQLException {
        if (datasource == null) {
            PoolProperties p = new PoolProperties();
            
            // JDBC URL aggiornato
            p.setUrl("jdbc:mysql://127.0.0.1:3306/second_chance?useSSL=false&allowPublicKeyRetrieval=true&serverTimezone=UTC");
            p.setDriverClassName("com.mysql.cj.jdbc.Driver");
            p.setUsername("root");
            p.setPassword("admin");
            
            // Pool settings
            p.setMaxActive(50);
            p.setInitialSize(5);
            p.setMinIdle(5);
            p.setMaxWait(10000);
            p.setRemoveAbandoned(true);
            p.setRemoveAbandonedTimeout(60);
            p.setLogAbandoned(true); // logga connessioni non chiuse
            
            datasource = new DataSource();
            datasource.setPoolProperties(p);
        }
        return datasource.getConnection();
    }
}
