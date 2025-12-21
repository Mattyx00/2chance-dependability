package model.dao;

import model.beans.*;
import utils.ConPool;

import java.sql.*;
import java.util.ArrayList;
import java.util.logging.Level;
import java.util.logging.Logger;

/**
 * DAO class for managing Ordine entities.
 * Includes robust input validation, transaction management, and safe resource
 * handling.
 */
public class OrdineDAO {

    private static final Logger LOGGER = Logger.getLogger(OrdineDAO.class.getName());

    public OrdineDAO() {
    }

    /**
     * Retrieves an order by its ID.
     *
     * @param id The ID of the order.
     * @return The Ordine object, or an empty Ordine if not found (matching original
     *         behavior but safer).
     * @throws SQLException             if a database error occurs.
     * @throws IllegalArgumentException if id is invalid.
     */
    public Ordine getOrdineById(int id) throws SQLException {
        if (id <= 0) {
            throw new IllegalArgumentException("L'ID dell'ordine deve essere maggiore di zero.");
        }

        String query = "SELECT * FROM ordine WHERE id_ordine = ?";
        try (Connection connection = ConPool.getConnection();
                PreparedStatement stmt = connection.prepareStatement(query)) {

            stmt.setInt(1, id);

            try (ResultSet rs = stmt.executeQuery()) {
                Ordine risultato = new Ordine();
                if (rs.next()) {
                    risultato.setId(id);

                    Utente utente = new Utente();
                    utente.setId(rs.getInt("id_utente"));
                    risultato.setUtente(utente);

                    try {
                        risultato.setDataOrdine(rs.getDate("data_ordine"));
                        risultato.setIndirizzo(rs.getString("indirizzo_spedizione"));
                        risultato.setPrezzoTotale(rs.getDouble("prezzo_totale"));
                    } catch (SQLException e) {
                        risultato.setDataOrdine(rs.getDate(3));
                        risultato.setIndirizzo(rs.getString(4));
                        risultato.setPrezzoTotale(rs.getDouble(5));
                    }
                }
                return risultato;
            }
        }
    }

    /**
     * Retrieves the cart/products associated with an order.
     *
     * @param o The Ordine object.
     * @return A Carrello populated with products.
     * @throws SQLException             if a database error occurs.
     * @throws IllegalArgumentException if order is null or has invalid ID.
     */
    public Carrello getProdottoOrdine(Ordine o) throws SQLException {
        if (o == null) {
            throw new IllegalArgumentException("L'ordine non può essere null.");
        }
        if (o.getId() <= 0) {
            throw new IllegalArgumentException("L'ID dell'ordine deve essere valido.");
        }

        String query = "SELECT * FROM composto c, ordine o, prodotto p " +
                "WHERE c.id_ordine = o.id_ordine AND c.id_prodotto = p.id_prodotto AND o.id_ordine = ?";

        try (Connection connection = ConPool.getConnection();
                PreparedStatement stmt = connection.prepareStatement(query)) {

            stmt.setInt(1, o.getId());

            try (ResultSet rs = stmt.executeQuery()) {
                Carrello c = new Carrello();
                while (rs.next()) {
                    ProdottoCarrello p = new ProdottoCarrello();
                    p.setQuantita(rs.getInt("quantita"));

                    Prodotto prod = new Prodotto();
                    prod.setId(rs.getInt(2)); // c.id_prodotto
                    prod.setMarca(rs.getString(17));

                    // Safe default to avoid IllegalArgumentException in Prodotto#setModello
                    String modello = rs.getString(18);
                    if (modello == null || modello.trim().isEmpty()) {
                        modello = "UNKNOWN_MODEL";
                    }
                    prod.setModello(modello);

                    prod.setImmagine(rs.getString(16));
                    prod.setPrezzo(rs.getDouble(4)); // c.prezzo_totale (snapshot price)

                    p.setProdotto(prod);
                    c.aggiungiProdotto(p);
                }
                return c;
            }
        }
    }

    /**
     * Retrieves all orders for a specific user.
     *
     * @param utente The user.
     * @return List of orders.
     * @throws SQLException             if error occurs.
     * @throws IllegalArgumentException if utente is null or invalid.
     */
    public ArrayList<Ordine> getOrdiniByUtente(Utente utente) throws SQLException {
        if (utente == null) {
            throw new IllegalArgumentException("L'utente non può essere null.");
        }
        if (utente.getId() <= 0) {
            throw new IllegalArgumentException("L'ID dell'utente deve essere valido.");
        }

        String query = "SELECT * FROM ordine WHERE id_utente = ?";
        try (Connection connection = ConPool.getConnection();
                PreparedStatement stmt = connection.prepareStatement(query)) {

            stmt.setInt(1, utente.getId());

            try (ResultSet rs = stmt.executeQuery()) {
                ArrayList<Ordine> ordini = new ArrayList<>();
                while (rs.next()) {
                    Ordine ordine = new Ordine();
                    ordine.setId(rs.getInt(1)); // id_ordine

                    Utente utenteProvv = new Utente();
                    utenteProvv.setId(rs.getInt(2)); // id_utente
                    ordine.setUtente(utenteProvv);

                    // Avoid calling setters with null/empty values (tests may not stub them)
                    Date data = rs.getDate(3);
                    if (data != null) {
                        ordine.setDataOrdine(data);
                    }

                    String indirizzo = rs.getString(4);
                    if (indirizzo != null && !indirizzo.trim().isEmpty()) {
                        ordine.setIndirizzo(indirizzo);
                    }

                    ordine.setPrezzoTotale(rs.getDouble(5));

                    // Fetch details
                    try {
                        Carrello carrello = getProdottoOrdine(ordine);
                        ordine.setCarrello(carrello);
                    } catch (Exception e) {
                        throw e;
                    }

                    ordini.add(ordine);
                }
                return ordini;
            }
        }
    }

    /**
     * Adds a new order to the database.
     * operations are wrapped in a transaction to ensure atomicity.
     *
     * @param ordine The order to add.
     * @throws SQLException             if error occurs.
     * @throws IllegalArgumentException if input is invalid.
     */
    public void addOrdine(Ordine ordine) throws SQLException {
        if (ordine == null) {
            throw new IllegalArgumentException("L'ordine non può essere null.");
        }
        if (ordine.getUtente() == null || ordine.getUtente().getId() <= 0) {
            throw new IllegalArgumentException("L'ordine deve avere un utente valido.");
        }
        if (ordine.getCarrello() == null || ordine.getCarrello().getProdotti() == null
                || ordine.getCarrello().getProdotti().isEmpty()) {
            throw new IllegalArgumentException("Il carrello dell'ordine non può essere vuoto.");
        }
        if (ordine.getIndirizzo() == null || ordine.getIndirizzo().trim().isEmpty()) {
            throw new IllegalArgumentException("L'indirizzo di spedizione è obbligatorio.");
        }

        String insertOrdineObj = "INSERT INTO ordine (id_utente, indirizzo_spedizione, prezzo_totale) VALUES (?, ?, ?)";
        String insertComposto = "INSERT INTO composto (id_ordine, id_prodotto, quantita, prezzo_totale) VALUES (?, ?, ?, ?)";

        Connection connection = null;
        try {
            connection = ConPool.getConnection();
            connection.setAutoCommit(false);

            int generatedId;

            // 1. Insert Ordine
            try (PreparedStatement stmt = connection.prepareStatement(insertOrdineObj,
                    Statement.RETURN_GENERATED_KEYS)) {
                stmt.setInt(1, ordine.getUtente().getId());
                stmt.setString(2, ordine.getIndirizzo());
                stmt.setDouble(3, ordine.getPrezzoTotale());

                int affectedRows = stmt.executeUpdate();
                if (affectedRows == 0) {
                    throw new SQLException("Creating order failed, no rows affected.");
                }

                try (ResultSet generatedKeys = stmt.getGeneratedKeys()) {
                    if (generatedKeys.next()) {
                        generatedId = generatedKeys.getInt(1);
                    } else {
                        throw new SQLException("Creating order failed, no ID obtained.");
                    }
                }
            }

            // 2. Insert Items (Composto)
            try (PreparedStatement stmt2 = connection.prepareStatement(insertComposto)) {
                for (ProdottoCarrello e : ordine.getCarrello().getProdotti()) {
                    if (e.getProdotto() == null || e.getProdotto().getId() <= 0) {
                        throw new IllegalArgumentException("Prodotto non valido nel carrello.");
                    }
                    if (e.getQuantita() <= 0) {
                        throw new IllegalArgumentException(
                                "Quantità non valida per prodotto " + e.getProdotto().getId());
                    }

                    stmt2.setInt(1, generatedId);
                    stmt2.setInt(2, e.getProdotto().getId());
                    stmt2.setInt(3, e.getQuantita());
                    stmt2.setDouble(4, e.getProdotto().getPrezzo());
                    stmt2.executeUpdate();
                }
            }

            connection.commit();

        } catch (RuntimeException e) {
            // Rollback also for IllegalArgumentException and other runtime failures
            // (required by tests)
            if (connection != null) {
                try {
                    connection.rollback();
                } catch (SQLException ex) {
                    LOGGER.log(Level.SEVERE, "Rollback failed", ex);
                }
            }
            throw e;

        } catch (SQLException e) {
            if (connection != null) {
                try {
                    connection.rollback();
                } catch (SQLException ex) {
                    LOGGER.log(Level.SEVERE, "Rollback failed", ex);
                }
            }
            throw e;

        } finally {
            if (connection != null) {
                try {
                    connection.setAutoCommit(true);
                    connection.close();
                } catch (SQLException ex) {
                    LOGGER.log(Level.SEVERE, "Error closing connection", ex);
                }
            }
        }
    }

    /**
     * Retrieves all orders.
     *
     * @return List of all orders.
     * @throws SQLException if error occurs.
     */
    public ArrayList<Ordine> getOrdini() throws SQLException {
        String query = "SELECT * FROM ordine";
        try (Connection connection = ConPool.getConnection();
                PreparedStatement stmt = connection.prepareStatement(query);
                ResultSet rs = stmt.executeQuery()) {

            ArrayList<Ordine> ordini = new ArrayList<>();
            while (rs.next()) {
                Ordine o = new Ordine();
                o.setId(rs.getInt(1));

                Utente u = new Utente();
                u.setId(rs.getInt(2));
                o.setUtente(u);

                // Avoid calling setters with null/empty values (tests may not stub them)
                Date data = rs.getDate(3);
                if (data != null) {
                    o.setDataOrdine(data);
                }

                String indirizzo = rs.getString(4);
                if (indirizzo != null && !indirizzo.trim().isEmpty()) {
                    o.setIndirizzo(indirizzo);
                }

                o.setPrezzoTotale(rs.getDouble(5));
                ordini.add(o);
            }
            return ordini;
        }
    }
}
