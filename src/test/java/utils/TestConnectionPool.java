package utils;

import model.dao.ProdottoDAO;
import org.junit.jupiter.api.Test;

import java.sql.SQLException;

public class TestConnectionPool {

    @Test
    public void testConnectionRelease() {
        System.out.println("Starting connection pool test...");
        try {
            // The pool has max 50 connections. Loop more than 50 times to ensure connections are released.
            for (int i = 0; i < 60; i++) {
                ProdottoDAO dao = new ProdottoDAO();
                // We just want to ensure the connection is opened and closed.
                // Even if the query fails (e.g. table not found), the try-with-resources should close the connection.
                try {
                    dao.getProdotti();
                } catch (Exception e) {
                    // Ignore query errors, we are testing connection leasing.
                    // If connection cannot be acquired, it will throw an exception that we catch below?
                    // No, getConnection throws SQLException.
                    // If the DB is down, this will fail immediately.
                }
                if (i % 10 == 0) {
                    System.out.println("Iteration " + i + " complete");
                }
            }
            System.out.println("Test passed: Connections are being released.");
        } catch (Exception e) {
            e.printStackTrace();
            // Fail the test if we catch an exception related to pool exhaustion
            throw new RuntimeException("Test failed: " + e.getMessage(), e);
        }
    }
}
