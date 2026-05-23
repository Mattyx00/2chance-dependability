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
                        "SELECT r.id_recensione, r.prodotto, r.data_recensione, r.testo, r.valutazione, p.categoria, p.descrizione, p.dimensioni, p.quantita, p.peso, p.immagine AS prodotto_immagine, p.marca, p.modello, p.prezzo FROM recensione r JOIN prodotto p ON r.prodotto = p.id_prodotto WHERE r.cliente = ?")) {
            stmt.setInt(1, utente.getId());
            ArrayList<Recensione> recensioni = new ArrayList<>();
            try (ResultSet rs = stmt.executeQuery()) {
                while (rs.next()) {
                    Recensione recensione = new Recensione();
                    recensione.setId(rs.getInt("id_recensione"));
                    
                    recensione.setUtente(utente);
                    
                    Prodotto prodottoProvvisorio = new Prodotto();
                    prodottoProvvisorio.setId(rs.getInt("prodotto"));
                    Categoria categoria = new Categoria();
                    categoria.setNomeCategoria(rs.getString("categoria"));
                    prodottoProvvisorio.setCategoria(categoria);
                    prodottoProvvisorio.setDescrizione(rs.getString("descrizione"));
                    prodottoProvvisorio.setDimensioni(rs.getString("dimensioni"));
                    prodottoProvvisorio.setQuantitaProdotto(rs.getInt("quantita"));
                    prodottoProvvisorio.setPeso(rs.getDouble("peso"));
                    prodottoProvvisorio.setImmagine(rs.getString("prodotto_immagine"));
                    prodottoProvvisorio.setMarca(rs.getString("marca"));
                    prodottoProvvisorio.setModello(rs.getString("modello"));
                    prodottoProvvisorio.setPrezzo(rs.getDouble("prezzo"));
                    recensione.setProdotto(prodottoProvvisorio);
                    
                    recensione.setDataRecensione(rs.getDate("data_recensione"));
                    recensione.setTesto(rs.getString("testo"));
                    recensione.setValutazione(rs.getInt("valutazione"));

                    recensioni.add(recensione);
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
                        "SELECT r.id_recensione, r.cliente, r.data_recensione, r.testo, r.valutazione, u.nome, u.cognome, u.admin, u.email, u.telefono, u.password, u.immagine AS utente_immagine FROM recensione r JOIN utente u ON r.cliente = u.id_utente WHERE r.prodotto = ?")) {
            stmt.setInt(1, prodotto.getId());
            ArrayList<Recensione> recensioni = new ArrayList<>();
            try (ResultSet rs = stmt.executeQuery()) {
                while (rs.next()) {
                    Recensione recensione = new Recensione();
                    recensione.setId(rs.getInt("id_recensione"));
                    
                    Utente utenteProvvisorio = new Utente();
                    utenteProvvisorio.setId(rs.getInt("cliente"));
                    utenteProvvisorio.setNome(rs.getString("nome"));
                    utenteProvvisorio.setCognome(rs.getString("cognome"));
                    utenteProvvisorio.setAdmin(rs.getBoolean("admin"));
                    utenteProvvisorio.setEmail(rs.getString("email"));
                    utenteProvvisorio.setTelefono(rs.getString("telefono"));
                    utenteProvvisorio.setPassword(rs.getString("password"));
                    utenteProvvisorio.setImmagine(rs.getString("utente_immagine"));
                    recensione.setUtente(utenteProvvisorio);
                    
                    recensione.setProdotto(prodotto);
                    
                    recensione.setDataRecensione(rs.getDate("data_recensione"));
                    recensione.setTesto(rs.getString("testo"));
                    recensione.setValutazione(rs.getInt("valutazione"));

                    recensioni.add(recensione);
                }
            }
            return recensioni;
        }
    }

    public int addRecensione(Recensione recensione) throws SQLException {
        validateRecensione(recensione);
        
        // Log before acquiring the connection to save DB connection hold time
        if (LOGGER.isLoggable(java.util.logging.Level.INFO)) {
            LOGGER.info("Adding review for user " + recensione.getUtente().getId() + " on product "
                    + recensione.getProdotto().getId());
        }

        try (Connection connection = ConPool.getConnection();
                PreparedStatement stmt = connection
                        .prepareStatement("INSERT INTO recensione (cliente, prodotto, testo, valutazione) VALUES (?, ?, ?, ?)")) {

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
        recensione.setId(rs.getInt("id_recensione"));

        Utente utenteProvvisorio = new Utente();
        utenteProvvisorio.setId(rs.getInt("cliente"));
        utenteProvvisorio.setNome(rs.getString("nome"));
        utenteProvvisorio.setCognome(rs.getString("cognome"));
        utenteProvvisorio.setAdmin(rs.getBoolean("admin"));
        utenteProvvisorio.setEmail(rs.getString("email"));
        utenteProvvisorio.setTelefono(rs.getString("telefono"));
        utenteProvvisorio.setPassword(rs.getString("password"));
        utenteProvvisorio.setImmagine(rs.getString("utente_immagine"));
        recensione.setUtente(utenteProvvisorio);

        Prodotto prodottoProvvisorio = new Prodotto();
        prodottoProvvisorio.setId(rs.getInt("prodotto"));
        Categoria categoria = new Categoria();
        categoria.setNomeCategoria(rs.getString("categoria"));
        prodottoProvvisorio.setCategoria(categoria);
        prodottoProvvisorio.setDescrizione(rs.getString("descrizione"));
        prodottoProvvisorio.setDimensioni(rs.getString("dimensioni"));
        prodottoProvvisorio.setQuantitaProdotto(rs.getInt("quantita"));
        prodottoProvvisorio.setPeso(rs.getDouble("peso"));
        prodottoProvvisorio.setImmagine(rs.getString("prodotto_immagine"));
        prodottoProvvisorio.setMarca(rs.getString("marca"));
        prodottoProvvisorio.setModello(rs.getString("modello"));
        prodottoProvvisorio.setPrezzo(rs.getDouble("prezzo"));
        recensione.setProdotto(prodottoProvvisorio);

        recensione.setDataRecensione(rs.getDate("data_recensione"));
        recensione.setTesto(rs.getString("testo"));
        recensione.setValutazione(rs.getInt("valutazione"));

        return recensione;
    }
}
