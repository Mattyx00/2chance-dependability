package model.dao;

import model.beans.Utente;
import utils.ConPool;

import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.util.ArrayList;

public class UtenteDAO {

    private static final java.util.logging.Logger LOGGER = java.util.logging.Logger
            .getLogger(UtenteDAO.class.getName());

    public UtenteDAO() {
    }

    public Utente getUtenteById(int id) throws SQLException {
        if (id <= 0) {
            throw new IllegalArgumentException("L'ID dell'utente deve essere maggiore di zero.");
        }
        try (Connection connection = ConPool.getConnection();
                PreparedStatement stmt = connection.prepareStatement("SELECT * FROM utente WHERE id_utente= ?")) {
            stmt.setInt(1, id);
            try (ResultSet rs = stmt.executeQuery()) {
                if (rs.next()) {
                    Utente utente = mapRowToUtente(rs);

                    // Load dependents safely
                    try {
                        OrdineDAO dao = getOrdineDAO();
                        utente.setOrdini(dao.getOrdiniByUtente(utente));
                    } catch (SQLException e) {
                        LOGGER.warning("Failed to load orders for user " + id + ": " + e.getMessage());
                        utente.setOrdini(new ArrayList<>());
                    }

                    try {
                        RecensioneDAO rDao = getRecensioneDAO();
                        utente.setRecensioni(rDao.getRecensioniByUtente(utente));
                    } catch (SQLException e) {
                        LOGGER.warning("Failed to load reviews for user " + id + ": " + e.getMessage());
                        utente.setRecensioni(new ArrayList<>());
                    }

                    return utente;
                }
            }
            return null;
        }
    }

    public ArrayList<Utente> getUtenti() throws SQLException {
        try (Connection connection = ConPool.getConnection();
                PreparedStatement stmt = connection.prepareStatement("SELECT * FROM utente")) {
            ArrayList<Utente> utenti = new ArrayList<>();
            try (ResultSet rs = stmt.executeQuery()) {
                while (rs.next()) {
                    utenti.add(mapRowToUtente(rs));
                }
            }
            return utenti;
        }
    }

    public int addUtente(Utente utente) throws SQLException {
        validateUtente(utente);

        String query;
        if (utente.getImmagine() == null) {
            query = "INSERT INTO utente VALUES (default, ?, ?, default, ?, ?, ?, default);";
        } else {
            query = "INSERT INTO utente VALUES (default, ?, ?, default, ?, ?, ?, ?);";
        }

        try (Connection connection = ConPool.getConnection();
                PreparedStatement stmt = connection.prepareStatement(query)) {
            stmt.setString(1, utente.getNome());
            stmt.setString(2, utente.getCognome());
            stmt.setString(3, utente.getEmail());
            stmt.setString(4, utente.getTelefono());
            stmt.setString(5, utente.getPassword());
            if (utente.getImmagine() != null) {
                stmt.setString(6, utente.getImmagine());
            }
            return stmt.executeUpdate();
        }
    }

    public Utente getUserByEmailPassword(String email, String password) throws SQLException {
        if (email == null || email.trim().isEmpty()) {
            throw new IllegalArgumentException("L'email non può essere null o vuota.");
        }
        if (password == null || password.trim().isEmpty()) {
            throw new IllegalArgumentException("La password non può essere null o vuota.");
        }

        try (Connection connection = ConPool.getConnection();
                PreparedStatement stmt = connection
                        .prepareStatement("SELECT * FROM utente WHERE email = ? AND passwordhash = SHA1(?)")) {
            stmt.setString(1, email);
            stmt.setString(2, password);
            try (ResultSet rs = stmt.executeQuery()) {
                if (rs.next()) {
                    Utente utente = mapRowToUtente(rs);

                    // Load dependents
                    try {
                        OrdineDAO dao = getOrdineDAO();
                        utente.setOrdini(dao.getOrdiniByUtente(utente));
                    } catch (SQLException e) {
                        LOGGER.warning("Failed to load orders for user " + utente.getId());
                        utente.setOrdini(new ArrayList<>());
                    }

                    try {
                        RecensioneDAO rDao = getRecensioneDAO();
                        utente.setRecensioni(rDao.getRecensioniByUtente(utente));
                    } catch (SQLException e) {
                        LOGGER.warning("Failed to load reviews for user " + utente.getId());
                        utente.setRecensioni(new ArrayList<>());
                    }

                    return utente;
                }
            }
            return null;
        }
    }

    public static boolean isEmailPresent(String email) throws SQLException {
        if (email == null || email.trim().isEmpty()) {
            throw new IllegalArgumentException("L'email non può essere null o vuota.");
        }
        try (Connection connection = ConPool.getConnection();
                PreparedStatement stmt = connection.prepareStatement("SELECT email FROM utente WHERE email = ?")) {
            stmt.setString(1, email);
            try (ResultSet rs = stmt.executeQuery()) {
                return rs.next();
            }
        }
    }

    public void editProfilo(String operation, String modifica, int idProfilo) throws SQLException {
        if (operation == null || operation.trim().isEmpty()) {
            throw new IllegalArgumentException("L'operazione non può essere null o vuota.");
        }
        if (modifica == null || modifica.trim().isEmpty()) {
            throw new IllegalArgumentException("La modifica non può essere null o vuota.");
        }
        if (idProfilo <= 0) {
            throw new IllegalArgumentException("L'ID del profilo deve essere maggiore di zero.");
        }

        String column = null;
        switch (operation) {
            case "/editNome":
                column = "nome";
                break;
            case "/editCognome":
                column = "cognome";
                break;
            case "/editEmail":
                column = "email";
                break;
            case "/editTelefono":
                column = "telefono";
                break;
            case "/editImmagine":
                column = "immagine";
                break;
            default:
                throw new IllegalArgumentException("Operazione non supportata: " + operation);
        }

        String sql = "UPDATE utente SET " + column + " = ? WHERE id_utente = ?";
        try (Connection connection = ConPool.getConnection();
                PreparedStatement stmt = connection.prepareStatement(sql)) {
            stmt.setString(1, modifica);
            stmt.setInt(2, idProfilo);
            stmt.executeUpdate();
        }
    }

    private void validateUtente(Utente utente) {
        if (utente == null) {
            throw new IllegalArgumentException("L'utente non può essere null.");
        }
        if (utente.getNome() == null || utente.getNome().trim().isEmpty()) {
            throw new IllegalArgumentException("Il nome dell'utente è obbligatorio.");
        }
        if (utente.getCognome() == null || utente.getCognome().trim().isEmpty()) {
            throw new IllegalArgumentException("Il cognome dell'utente è obbligatorio.");
        }
        if (utente.getEmail() == null || utente.getEmail().trim().isEmpty()) {
            throw new IllegalArgumentException("L'email dell'utente è obbligatoria.");
        }
        if (utente.getPassword() == null || utente.getPassword().trim().isEmpty()) {
            throw new IllegalArgumentException("La password dell'utente è obbligatoria.");
        }
    }

    private Utente mapRowToUtente(ResultSet rs) throws SQLException {
        Utente utente = new Utente();
        utente.setId(rs.getInt(1));
        utente.setNome(rs.getString(2));
        utente.setCognome(rs.getString(3));
        utente.setAdmin(rs.getBoolean(4));
        utente.setEmail(rs.getString(5));
        utente.setTelefono(rs.getString(6));
        utente.setPassword(rs.getString(7));
        utente.setImmagine(rs.getString(8));
        return utente;
    }

    // Protected methods for testability (Partial Mocking)
    protected OrdineDAO getOrdineDAO() {
        return new OrdineDAO();
    }

    protected RecensioneDAO getRecensioneDAO() {
        return new RecensioneDAO();
    }
}
