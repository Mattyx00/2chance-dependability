package model.dao;

import model.beans.Utente;
import utils.ConPool;

import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.util.ArrayList;

public class UtenteDAO {

    public UtenteDAO() {
    }

    public Utente getUtenteById(int id) throws SQLException {
        if (id <= 0) {
            throw new IllegalArgumentException("L'ID dell'utente deve essere maggiore di zero");
        }
        try (Connection connection = ConPool.getConnection();
                PreparedStatement stmt = connection.prepareStatement("SELECT * FROM utente WHERE id_utente= ?")) {
            stmt.setInt(1, id);
            ResultSet rs = stmt.executeQuery();

            if (rs.next()) {
                Utente utente = new Utente();
                utente.setId(rs.getInt(1));
                utente.setNome(rs.getString(2));
                utente.setCognome(rs.getString(3));
                utente.setAdmin(rs.getBoolean(4));
                utente.setEmail(rs.getString(5));
                utente.setTelefono(rs.getString(6));
                utente.setPassword(rs.getString(7));
                utente.setImmagine(rs.getString(8));

                OrdineDAO dao = new OrdineDAO();
                utente.setOrdini(dao.getOrdiniByUtente(utente));

                RecensioneDAO rDao = new RecensioneDAO();
                utente.setRecensioni(rDao.getRecensioniByUtente(utente));
                return utente;
            }
            return null;
        }
    }

    public ArrayList<Utente> getUtenti() throws SQLException {
        try (Connection connection = ConPool.getConnection();
                PreparedStatement stmt = connection.prepareStatement("SELECT * FROM utente")) {
            ResultSet rs = stmt.executeQuery();
            ArrayList<Utente> utenti = new ArrayList<>();

            while (rs.next()) {
                Utente utente = new Utente();
                utente.setId(rs.getInt(1));
                utente.setNome(rs.getString(2));
                utente.setCognome(rs.getString(3));
                utente.setAdmin(rs.getBoolean(4));
                utente.setEmail(rs.getString(5));
                utente.setTelefono(rs.getString(6));
                utente.setPassword(rs.getString(7));
                utente.setImmagine(rs.getString(8));
                utenti.add(utente);
            }
            return utenti;
        }
    }

    public int addUtente(Utente utente) throws SQLException {
        if (utente == null) {
            throw new IllegalArgumentException("L'utente non può essere null");
        }
        String query = "";
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
            throw new IllegalArgumentException("L'email non può essere null o vuota");
        }
        if (password == null || password.trim().isEmpty()) {
            throw new IllegalArgumentException("La password non può essere null o vuota");
        }

        try (Connection connection = ConPool.getConnection();
                PreparedStatement stmt = connection
                        .prepareStatement("SELECT * FROM utente WHERE email = ? AND passwordhash = SHA1(?)")) {
            stmt.setString(1, email);
            stmt.setString(2, password);
            ResultSet rs = stmt.executeQuery();

            if (rs.next()) {
                Utente utente = new Utente();
                utente.setId(rs.getInt(1));
                utente.setNome(rs.getString(2));
                utente.setCognome(rs.getString(3));
                utente.setAdmin(rs.getBoolean(4));
                utente.setEmail(rs.getString(5));
                utente.setTelefono(rs.getString(6));
                utente.setPassword(rs.getString(7));
                utente.setImmagine(rs.getString(8));

                OrdineDAO dao = new OrdineDAO();
                utente.setOrdini(dao.getOrdiniByUtente(utente));
                RecensioneDAO rDao = new RecensioneDAO();
                utente.setRecensioni(rDao.getRecensioniByUtente(utente));

                return utente;
            }
            return null;
        }
    }

    public static boolean isEmailPresent(String email) throws SQLException {
        if (email == null || email.trim().isEmpty()) {
            throw new IllegalArgumentException("L'email non può essere null o vuota");
        }
        try (Connection connection = ConPool.getConnection();
                PreparedStatement stmt = connection.prepareStatement("SELECT email FROM utente WHERE email = ?")) {
            stmt.setString(1, email);
            ResultSet rs = stmt.executeQuery();

            if (!rs.next()) {
                return false;
            }

            else
                return true;
        }
    }

    public void editProfilo(String operation, String modifica, int idProfilo) throws SQLException {
        if (operation == null || operation.trim().isEmpty()) {
            throw new IllegalArgumentException("L'operazione non può essere null o vuota");
        }
        if (modifica == null || modifica.trim().isEmpty()) {
            throw new IllegalArgumentException("La modifica non può essere null o vuota");
        }
        if (idProfilo <= 0) {
            throw new IllegalArgumentException("L'ID del profilo deve essere maggiore di zero");
        }
        try (Connection connection = ConPool.getConnection()) {

            if (operation.equals("/editNome")) {
                try (PreparedStatement stmt = connection
                        .prepareStatement("UPDATE utente SET nome = ? WHERE id_utente = ?")) {
                    stmt.setString(1, modifica);
                    stmt.setInt(2, idProfilo);
                    stmt.executeUpdate();
                }
            }

            if (operation.equals("/editCognome")) {
                try (PreparedStatement stmt = connection
                        .prepareStatement("UPDATE utente SET cognome = ? WHERE id_utente = ?")) {
                    stmt.setString(1, modifica);
                    stmt.setInt(2, idProfilo);
                    stmt.executeUpdate();
                }
            }

            else if (operation.equals("/editEmail")) {
                try (PreparedStatement stmt = connection
                        .prepareStatement("UPDATE utente SET email = ? WHERE id_utente = ?")) {
                    stmt.setString(1, modifica);
                    stmt.setInt(2, idProfilo);
                    stmt.executeUpdate();
                }
            }

            else if (operation.equals("/editTelefono")) {
                try (PreparedStatement stmt = connection
                        .prepareStatement("UPDATE utente SET telefono = ? WHERE id_utente = ?")) {
                    stmt.setString(1, modifica);
                    stmt.setInt(2, idProfilo);
                    stmt.executeUpdate();
                }
            }

            else if (operation.equals("/editImmagine")) {
                try (PreparedStatement stmt = connection
                        .prepareStatement("UPDATE utente SET immagine = ? WHERE id_utente = ?")) {
                    stmt.setString(1, modifica);
                    stmt.setInt(2, idProfilo);
                    stmt.executeUpdate();
                }
            }
        }
    }

}
