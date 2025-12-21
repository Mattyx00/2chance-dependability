package model.dao;

import model.beans.Categoria;
import model.beans.Prodotto;
import model.beans.Recensione;
import model.beans.Utente;
import utils.ConPool;

import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.util.ArrayList;
import java.util.logging.Logger;

/**
 * DAO class for managing Recensione entities.
 * Includes defensive programming, validation, and safe resource handling.
 */
public class RecensioneDAO {

    private static final Logger LOGGER = Logger.getLogger(RecensioneDAO.class.getName());

    public RecensioneDAO() {
    }

    public ArrayList<Recensione> getRecensioniByUtente(Utente utente) throws SQLException {
        if (utente == null || utente.getId() <= 0) {
            throw new IllegalArgumentException("L'utente non può essere null e deve avere un ID valido.");
        }
        try (Connection connection = ConPool.getConnection();
                PreparedStatement stmt = connection.prepareStatement(
                        "SELECT * FROM recensione, utente, prodotto WHERE recensione.cliente = ? AND recensione.cliente = utente.id_utente AND recensione.prodotto = prodotto.id_prodotto")) {
            stmt.setInt(1, utente.getId());
            ArrayList<Recensione> recensioni = new ArrayList<>();
            try (ResultSet rs = stmt.executeQuery()) {
                while (rs.next()) {
                    recensioni.add(mapRowToRecensione(rs));
                }
            }
            return recensioni;
        }
    }

    public ArrayList<Recensione> getRecensioniByProdotto(Prodotto prodotto) throws SQLException {
        if (prodotto == null || prodotto.getId() <= 0) {
            throw new IllegalArgumentException("Il prodotto non può essere null e deve avere un ID valido.");
        }
        try (Connection connection = ConPool.getConnection();
                PreparedStatement stmt = connection.prepareStatement(
                        "SELECT * FROM recensione, utente, prodotto WHERE recensione.prodotto = ? AND recensione.cliente = utente.id_utente AND recensione.prodotto = prodotto.id_prodotto")) {
            stmt.setInt(1, prodotto.getId());
            ArrayList<Recensione> recensioni = new ArrayList<>();
            try (ResultSet rs = stmt.executeQuery()) {
                while (rs.next()) {
                    recensioni.add(mapRowToRecensione(rs));
                }
            }
            return recensioni;
        }
    }

    public int addRecensione(Recensione recensione) throws SQLException {
        validateRecensione(recensione);
        try (Connection connection = ConPool.getConnection();
                PreparedStatement stmt = connection
                        .prepareStatement("INSERT INTO recensione VALUES (default, ?, ?, default, ?, ?)")) {
            // Replaced System.out.println with Logger or removed if purely debug
            LOGGER.info("Adding review for user " + recensione.getUtente().getId() + " on product "
                    + recensione.getProdotto().getId());

            stmt.setInt(1, recensione.getUtente().getId());
            stmt.setInt(2, recensione.getProdotto().getId());
            stmt.setString(3, recensione.getTesto());
            stmt.setInt(4, recensione.getValutazione());
            return stmt.executeUpdate();
        }
    }

    public void deleteRecensione(int idRecensione) throws SQLException {
        if (idRecensione <= 0) {
            throw new IllegalArgumentException("L'ID della recensione deve essere maggiore di zero.");
        }
        try (Connection connection = ConPool.getConnection();
                PreparedStatement stmt = connection
                        .prepareStatement("DELETE FROM recensione WHERE id_recensione = ?")) {
            stmt.setInt(1, idRecensione);
            stmt.executeUpdate();
        }
    }

    private void validateRecensione(Recensione r) {
        if (r == null) {
            throw new IllegalArgumentException("La recensione non può essere null.");
        }
        if (r.getUtente() == null || r.getUtente().getId() <= 0) {
            throw new IllegalArgumentException("La recensione deve essere associata a un utente valido.");
        }
        if (r.getProdotto() == null || r.getProdotto().getId() <= 0) {
            throw new IllegalArgumentException("La recensione deve essere associata a un prodotto valido.");
        }
        if (r.getTesto() == null || r.getTesto().trim().isEmpty()) {
            throw new IllegalArgumentException("Il testo della recensione è obbligatorio.");
        }
        if (r.getValutazione() < 1 || r.getValutazione() > 5) {
            throw new IllegalArgumentException("La valutazione deve essere compresa tra 1 e 5.");
        }
    }

    private Recensione mapRowToRecensione(ResultSet rs) throws SQLException {
        Recensione recensione = new Recensione();
        recensione.setId(rs.getInt(1));

        Utente utenteProvvisorio = new Utente();
        utenteProvvisorio.setId(rs.getInt(2));
        utenteProvvisorio.setNome(rs.getString(8));
        utenteProvvisorio.setCognome(rs.getString(9));
        utenteProvvisorio.setAdmin(rs.getBoolean(10));
        utenteProvvisorio.setEmail(rs.getString(11));
        utenteProvvisorio.setTelefono(rs.getString(12));
        utenteProvvisorio.setPassword(rs.getString(13));
        utenteProvvisorio.setImmagine(rs.getString(14));
        recensione.setUtente(utenteProvvisorio);

        Prodotto prodottoProvvisorio = new Prodotto();
        prodottoProvvisorio.setId(rs.getInt(3));
        Categoria categoria = new Categoria();
        categoria.setNomeCategoria(rs.getString(16));
        prodottoProvvisorio.setCategoria(categoria);
        prodottoProvvisorio.setDescrizione(rs.getString(17));
        prodottoProvvisorio.setDimensioni(rs.getString(18));
        prodottoProvvisorio.setQuantitaProdotto(rs.getInt(19));
        // Improved precision by using getDouble for weight if compatible with bean
        prodottoProvvisorio.setPeso(rs.getDouble(20));
        prodottoProvvisorio.setImmagine(rs.getString(21));
        prodottoProvvisorio.setMarca(rs.getString(22));
        prodottoProvvisorio.setModello(rs.getString(23));
        prodottoProvvisorio.setPrezzo(rs.getDouble(24));
        recensione.setProdotto(prodottoProvvisorio);

        recensione.setDataRecensione(rs.getDate(4));
        recensione.setTesto(rs.getString(5));
        recensione.setValutazione(rs.getInt(6));

        return recensione;
    }
}
