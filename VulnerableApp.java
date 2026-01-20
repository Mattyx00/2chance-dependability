package com.example;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.sql.Connection;
import java.sql.DriverManager;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Statement;

public class VulnerableApp {

    // 1. HARDCODED SECRET (Snyk e GitGuardian lo troveranno)
    private static final String AWS_ACCESS_KEY = "AKIAIOSFODNN7EXAMPLE";
    private static final String DB_PASSWORD = "password123";

    public void unsafeDatabaseQuery(String username) throws SQLException {
        Connection conn = DriverManager.getConnection("jdbc:mysql://localhost:3306/db", "root", DB_PASSWORD);
        Statement stmt = conn.createStatement();

        // 2. SQL INJECTION (Snyk Code: High Severity)
        // Concatenare stringhe in una query permette agli hacker di manipolare il DB
        String query = "SELECT * FROM users WHERE username = '" + username + "'";
        ResultSet rs = stmt.executeQuery(query);
    }

    public void weakCryptography(String password) throws NoSuchAlgorithmException {
        // 3. WEAK HASHING (Snyk Code: Medium Severity)
        // MD5 è considerato rotto e insicuro per le password
        MessageDigest md = MessageDigest.getInstance("MD5");
        md.update(password.getBytes());
        byte[] digest = md.digest();
    }

    public void pathTraversal(String filename) throws IOException {
        // 4. PATH TRAVERSAL (Snyk Code: High Severity)
        // Un utente potrebbe passare "../../etc/passwd" e leggere file di sistema
        File file = new File("/var/www/uploads/" + filename);
        FileInputStream fis = new FileInputStream(file);
        fis.read();
    }

    public static void main(String[] args) {
        System.out.println("App Vulnerabile Avviata...");
    }
}