package services;

import model.beans.Utente;
import model.dao.UtenteDAO;
import utils.LoginErratoException;

import java.sql.SQLException;

public class LoginService {
    private final UtenteDAO utenteDAO;

    /**
     * Constructs a LoginService with a default UtenteDAO.
     * 
     * @throws SQLException if a database access error occurs during DAO creation.
     */
    public LoginService() throws SQLException {
        this.utenteDAO = new UtenteDAO();
    }

    /**
     * Constructs a LoginService with a specific UtenteDAO.
     *
     * @param utenteDAO the DAO to be used, must not be null.
     * @throws IllegalArgumentException if utenteDAO is null.
     */
    public LoginService(UtenteDAO utenteDAO) {
        if (utenteDAO == null) {
            throw new IllegalArgumentException("UtenteDAO cannot be null");
        }
        this.utenteDAO = utenteDAO;
    }

    /**
     * Authenticates a user with the given email and password.
     *
     * @param email    the user's email, must not be null or empty.
     * @param password the user's password, must not be null or empty.
     * @return the authenticated Utente object.
     * @throws SQLException             if a database access error occurs.
     * @throws LoginErratoException     if the credentials are invalid (user not
     *                                  found).
     * @throws IllegalArgumentException if email or password are null or empty.
     */
    public Utente login(String email, String password) throws SQLException, LoginErratoException {
        if (email == null || email.trim().isEmpty()) {
            throw new IllegalArgumentException("Email cannot be null or empty");
        }
        if (password == null || password.trim().isEmpty()) {
            throw new IllegalArgumentException("Password cannot be null or empty");
        }

        Utente utente = utenteDAO.getUserByEmailPassword(email, password);
        if (utente == null) {
            throw new LoginErratoException();
        }
        return utente;
    }
}
