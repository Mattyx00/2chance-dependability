package model.dao;

import model.beans.Categoria;
import model.beans.Prodotto;
import model.beans.Specifiche;
import utils.ConPool;

import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.util.ArrayList;
import java.util.logging.Level;
import java.util.logging.Logger;

/**
 * DAO class for managing Prodotto entities.
 * Includes defensive programming, validation, and safe resource handling.
 */
public class ProdottoDAO {

    private static final Logger LOGGER = Logger.getLogger(ProdottoDAO.class.getName());

    public ProdottoDAO() {
    }

    public ArrayList<Prodotto> getProdotti() throws SQLException {
        try (Connection connection = ConPool.getConnection();
                PreparedStatement stmt = connection.prepareStatement("SELECT * FROM prodotto WHERE disabilitato = 0")) {
            ArrayList<Prodotto> prodotti = new ArrayList<>();
            try (ResultSet rs = stmt.executeQuery()) {
                while (rs.next()) {
                    prodotti.add(mapRowToProdotto(rs));
                }
            }
            return prodotti;
        }
    }

    public Prodotto getProdottoById(int idProdotto) throws SQLException {
        if (idProdotto <= 0) {
            throw new IllegalArgumentException("L'ID del prodotto deve essere maggiore di zero.");
        }
        try (Connection connection = ConPool.getConnection();
                PreparedStatement stmt = connection
                        .prepareStatement("SELECT * FROM prodotto WHERE id_prodotto = ? AND disabilitato = 0")) {
            stmt.setInt(1, idProdotto);
            try (ResultSet rs = stmt.executeQuery()) {
                if (rs.next()) {
                    Prodotto p = mapRowToProdotto(rs);

                    // Fetch associated data safely
                    try {
                        SpecificheDAO dao = new SpecificheDAO();
                        p.setSpecifiche(dao.getSpecificheByProd(idProdotto));
                    } catch (SQLException e) {
                        LOGGER.log(Level.WARNING, "Failed to load specifics for product " + idProdotto, e);
                        p.setSpecifiche(new ArrayList<>());
                    }

                    try {
                        RecensioneDAO rdao = new RecensioneDAO();
                        p.setRecensioni(rdao.getRecensioniByProdotto(p));
                    } catch (SQLException e) {
                        LOGGER.log(Level.WARNING, "Failed to load reviews for product " + idProdotto, e);
                        p.setRecensioni(new ArrayList<>());
                    }

                    return p;
                }
                return null;
            }
        }
    }

    public ArrayList<Prodotto> getProdottiByCategoria(String categoria) throws SQLException {
        if (categoria == null || categoria.trim().isEmpty()) {
            throw new IllegalArgumentException("La categoria non può essere null o vuota.");
        }
        try (Connection connection = ConPool.getConnection();
                PreparedStatement stmt = connection
                        .prepareStatement("SELECT * FROM prodotto WHERE categoria = ? AND disabilitato = 0")) {
            stmt.setString(1, categoria);
            ArrayList<Prodotto> prodotti = new ArrayList<>();
            try (ResultSet rs = stmt.executeQuery()) {
                while (rs.next()) {
                    prodotti.add(mapRowToProdotto(rs));
                }
            }
            return prodotti;
        }
    }

    public int addProdotto(Prodotto p) throws SQLException {
        validateProdotto(p);

        // Columns: categoria, descrizione, dimensioni, quantita, peso, immagine, marca,
        // modello, prezzo, disabilitato
        String query = "INSERT INTO prodotto (categoria, descrizione, dimensioni, quantita, peso, immagine, marca, modello, prezzo, disabilitato) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, 0)";

        try (Connection connection = ConPool.getConnection();
                PreparedStatement stmt = connection.prepareStatement(query)) {
            stmt.setString(1, p.getCategoria().getNomeCategoria());
            stmt.setString(2, p.getDescrizione());
            stmt.setString(3, p.getDimensioni());
            stmt.setInt(4, p.getQuantitaProdotto());
            stmt.setDouble(5, p.getPeso());
            stmt.setString(6, p.getImmagine());
            stmt.setString(7, p.getMarca());
            stmt.setString(8, p.getModello());
            stmt.setDouble(9, p.getPrezzo());

            return stmt.executeUpdate();
        }
    }

    public ArrayList<Prodotto> getUltimiProdotti() throws SQLException {
        try (Connection connection = ConPool.getConnection();
                PreparedStatement stmt = connection.prepareStatement(
                        "SELECT * FROM prodotto WHERE disabilitato = 0 ORDER BY id_prodotto DESC LIMIT 8")) {
            ArrayList<Prodotto> prodotti = new ArrayList<>();
            try (ResultSet rs = stmt.executeQuery()) {
                while (rs.next()) {
                    prodotti.add(mapRowToProdotto(rs));
                }
            }
            return prodotti;
        }
    }

    public ArrayList<Prodotto> cercaProdotti(String nome) throws SQLException {
        if (nome == null || nome.trim().isEmpty()) {
            throw new IllegalArgumentException("Il nome di ricerca non può essere null o vuoto.");
        }
        try (Connection connection = ConPool.getConnection();
                PreparedStatement stmt = connection.prepareStatement(
                        "SELECT * FROM prodotto WHERE UPPER(CONCAT(marca, modello, descrizione, categoria)) LIKE UPPER(?) AND disabilitato = 0")) {
            // Preserving strict behavior of original code for 'nome' passing
            // but assuming intent is to find substring if wildcard passed or logical match
            stmt.setString(1, nome);

            ArrayList<Prodotto> prodotti = new ArrayList<>();
            try (ResultSet rs = stmt.executeQuery()) {
                while (rs.next()) {
                    prodotti.add(mapRowToProdotto(rs));
                }
            }
            return prodotti;
        }
    }

    public void eliminaProdotto(int idProdotto) throws SQLException {
        if (idProdotto <= 0) {
            throw new IllegalArgumentException("L'ID del prodotto deve essere maggiore di zero.");
        }
        try (Connection connection = ConPool.getConnection();
                PreparedStatement stmt = connection
                        .prepareStatement("UPDATE prodotto SET disabilitato = 1 WHERE id_prodotto = ?")) {
            stmt.setInt(1, idProdotto);
            stmt.executeUpdate();
        }
    }

    public void aggiungiSpecifiche(ArrayList<Specifiche> specifiche, int idProdotto) throws SQLException {
        if (specifiche == null) {
            throw new IllegalArgumentException("La lista delle specifiche non può essere null.");
        }
        if (idProdotto <= 0) {
            throw new IllegalArgumentException("L'ID del prodotto deve essere maggiore di zero.");
        }
        try (Connection connection = ConPool.getConnection();
                PreparedStatement stmt = connection
                        .prepareStatement("INSERT INTO specifiche (nome, id_prodotto, valore) VALUES (?, ?, ?)")) {

            for (Specifiche s : specifiche) {
                if (s == null || s.getNome() == null || s.getValore() == null) {
                    continue; // Skip invalid entries
                }
                stmt.setString(1, s.getNome());
                stmt.setInt(2, idProdotto);
                stmt.setString(3, s.getValore());
                stmt.executeUpdate();
            }
        }
    }

    public int getLastProduct() throws SQLException {
        try (Connection connection = ConPool.getConnection();
                PreparedStatement stmt = connection
                        .prepareStatement("SELECT MAX(id_prodotto) FROM prodotto WHERE disabilitato = 0")) {
            try (ResultSet rs = stmt.executeQuery()) {
                if (rs.next()) {
                    return rs.getInt(1);
                }
                return 0; // Or throw, but 0 indicates no product found safely
            }
        }
    }

    public int eliminaSpecificheProdotto(int idProdotto) throws SQLException {
        if (idProdotto <= 0) {
            throw new IllegalArgumentException("L'ID del prodotto deve essere maggiore di zero.");
        }
        try (Connection connection = ConPool.getConnection();
                PreparedStatement stmt = connection.prepareStatement("DELETE FROM specifiche WHERE id_prodotto = ?")) {
            stmt.setInt(1, idProdotto);
            return stmt.executeUpdate();
        }
    }

    public void modificaProdotto(Prodotto p) throws SQLException {
        validateProdotto(p);
        if (p.getId() <= 0) {
            throw new IllegalArgumentException("L'ID del prodotto deve essere valido per la modifica.");
        }

        boolean updateImage = p.getImmagine() != null && !p.getImmagine().trim().isEmpty();
        String query;

        if (updateImage) {
            query = "UPDATE prodotto SET marca = ?, modello = ?, prezzo = ?, descrizione = ?, dimensioni = ?, peso = ?, categoria = ?, immagine = ? WHERE id_prodotto = ?";
        } else {
            query = "UPDATE prodotto SET marca = ?, modello = ?, prezzo = ?, descrizione = ?, dimensioni = ?, peso = ?, categoria = ? WHERE id_prodotto = ?";
        }

        try (Connection connection = ConPool.getConnection();
                PreparedStatement stmt = connection.prepareStatement(query)) {
            stmt.setString(1, p.getMarca());
            stmt.setString(2, p.getModello());
            stmt.setDouble(3, p.getPrezzo());
            stmt.setString(4, p.getDescrizione());
            stmt.setString(5, p.getDimensioni());
            stmt.setDouble(6, p.getPeso());
            stmt.setString(7, p.getCategoria().getNomeCategoria());

            if (updateImage) {
                stmt.setString(8, p.getImmagine());
                stmt.setInt(9, p.getId());
            } else {
                stmt.setInt(8, p.getId());
            }

            stmt.executeUpdate();
        }
    }

    // Helper methods for validation and mapping

    private void validateProdotto(Prodotto p) {
        if (p == null) {
            throw new IllegalArgumentException("Il prodotto non può essere null.");
        }
        if (p.getCategoria() == null || p.getCategoria().getNomeCategoria() == null
                || p.getCategoria().getNomeCategoria().trim().isEmpty()) {
            throw new IllegalArgumentException("Il prodotto deve avere una categoria valida.");
        }
        if (p.getMarca() == null || p.getMarca().trim().isEmpty()) {
            throw new IllegalArgumentException("La marca del prodotto è obbligatoria.");
        }
        if (p.getModello() == null || p.getModello().trim().isEmpty()) {
            throw new IllegalArgumentException("Il modello del prodotto è obbligatorio.");
        }
        if (p.getDescrizione() == null) {
            // Optional but safe to init empty or check if required?
            // Original code didn't check. Robustness suggests ensuring it's not strictly
            // null if used later.
            // But strict validation on business logic often allows empty description. We'll
            // allow null in logic, but setString might prefer valid string.
            // Let's assume description can be null, but keeping it as is.
        }
        if (p.getPrezzo() < 0) {
            throw new IllegalArgumentException("Il prezzo del prodotto non può essere negativo.");
        }
    }

    private Prodotto mapRowToProdotto(ResultSet rs) throws SQLException {
        Prodotto p = new Prodotto();
        Categoria c = new Categoria();

        p.setId(rs.getInt(1)); // id_prodotto

        String catName = rs.getString(2); // categoria
        c.setNomeCategoria(catName != null ? catName : "Unknown");
        p.setCategoria(c);

        p.setDescrizione(rs.getString(3));
        p.setDimensioni(rs.getString(4));
        p.setQuantitaProdotto(rs.getInt(5));
        p.setPeso(rs.getDouble(6));
        p.setImmagine(rs.getString(7));
        p.setMarca(rs.getString(8));
        p.setModello(rs.getString(9));
        p.setPrezzo(rs.getDouble(10));

        return p;
    }
}
