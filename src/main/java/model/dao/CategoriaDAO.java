package model.dao;

import model.beans.Categoria;
import utils.ConPool;

import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.util.ArrayList;

public class CategoriaDAO {

    public CategoriaDAO() {
    }

    public ArrayList<Categoria> getCategorie() throws SQLException {
        try (Connection connection = ConPool.getConnection();
                PreparedStatement stmt = connection.prepareStatement("SELECT * FROM categoria")) {

            ArrayList<Categoria> categorie = new ArrayList<>();
            ResultSet set = stmt.executeQuery();

            while (set.next()) {
                String nomeCategoria = set.getString(1);
                // Defensive check: ensure data from DB is valid
                if (nomeCategoria != null && !nomeCategoria.trim().isEmpty()) {
                    Categoria c = new Categoria();
                    c.setNomeCategoria(nomeCategoria);
                    categorie.add(c);
                }
            }
            return categorie;
        }
    }

    public int addCategoria(Categoria c) throws SQLException {
        if (c == null) {
            throw new IllegalArgumentException("Il parametro 'categoria' non può essere null.");
        }
        if (c.getNomeCategoria() == null || c.getNomeCategoria().trim().isEmpty()) {
            throw new IllegalArgumentException("Il nome della categoria non può essere null o vuoto.");
        }

        try (Connection connection = ConPool.getConnection();
                PreparedStatement stmt = connection.prepareStatement("INSERT INTO categoria VALUES (?)")) {
            stmt.setString(1, c.getNomeCategoria());
            return stmt.executeUpdate();
        }
    }

    public void eliminaCategoria(String nome) throws SQLException {
        if (nome == null || nome.trim().isEmpty()) {
            throw new IllegalArgumentException("Il parametro 'nome' non può essere null o vuoto.");
        }

        try (Connection connection = ConPool.getConnection();
                PreparedStatement stmt = connection.prepareStatement("DELETE FROM categoria WHERE nome = ?")) {
            stmt.setString(1, nome);

            stmt.executeUpdate();
        }
    }

}
