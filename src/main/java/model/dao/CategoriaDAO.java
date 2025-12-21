package model.dao;

import model.beans.Categoria;
import utils.ConPool;

import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.util.ArrayList;

/**
 * DAO class for managing Categoria entities.
 * Implements defensive programming ensuring robust input validation and safe
 * database interactions.
 */
public class CategoriaDAO {

    public CategoriaDAO() {
    }

    /**
     * Retrieves all categories from the database.
     * Skips invalid entries found in the database ensuring the returned list
     * contains only valid objects.
     *
     * @return ArrayList of Categoria objects.
     * @throws SQLException if a database access error occurs.
     */
    public ArrayList<Categoria> getCategorie() throws SQLException {
        try (Connection connection = ConPool.getConnection();
                PreparedStatement stmt = connection.prepareStatement("SELECT * FROM categoria")) {

            ArrayList<Categoria> categorie = new ArrayList<>();
            try (ResultSet set = stmt.executeQuery()) {
                while (set.next()) {
                    String nomeCategoria = set.getString(1);

                    // Defensive check: ensure data from DB is valid before creating object
                    if (isValidCategoriaName(nomeCategoria)) {
                        Categoria c = new Categoria();
                        c.setNomeCategoria(nomeCategoria);
                        categorie.add(c);
                    }
                }
            }
            return categorie;
        }
    }

    /**
     * Adds a new category to the database.
     * Validates input strictly.
     *
     * @param c The Categoria object to add.
     * @return the row count for SQL Data Manipulation Language (DML) statements.
     * @throws SQLException             if a database access error occurs.
     * @throws IllegalArgumentException if the Categoria object is null or has
     *                                  invalid data.
     */
    public int addCategoria(Categoria c) throws SQLException {
        if (c == null) {
            throw new IllegalArgumentException("Il parametro 'categoria' non può essere null.");
        }
        if (!isValidCategoriaName(c.getNomeCategoria())) {
            throw new IllegalArgumentException("Il nome della categoria non può essere null o vuoto.");
        }

        try (Connection connection = ConPool.getConnection();
                PreparedStatement stmt = connection.prepareStatement("INSERT INTO categoria VALUES (?)")) {
            stmt.setString(1, c.getNomeCategoria());
            return stmt.executeUpdate();
        }
    }

    /**
     * Deletes a category from the database.
     * Validates input strictly.
     *
     * @param nome The name of the category to delete.
     * @throws SQLException             if a database access error occurs.
     * @throws IllegalArgumentException if the 'nome' parameter is null or empty.
     */
    public void eliminaCategoria(String nome) throws SQLException {
        if (!isValidCategoriaName(nome)) {
            throw new IllegalArgumentException("Il parametro 'nome' non può essere null o vuoto.");
        }

        try (Connection connection = ConPool.getConnection();
                PreparedStatement stmt = connection.prepareStatement("DELETE FROM categoria WHERE nome = ?")) {
            stmt.setString(1, nome);
            stmt.executeUpdate();
        }
    }

    /**
     * Helper method to validate category names.
     *
     * @param name The name to check.
     * @return true if valid, false otherwise.
     */
    private boolean isValidCategoriaName(String name) {
        return name != null && !name.trim().isEmpty();
    }
}
