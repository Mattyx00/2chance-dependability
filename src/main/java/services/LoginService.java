package services;

import model.beans.Utente;
import model.dao.UtenteDAO;
import utils.LoginErratoException;

import java.sql.SQLException;

public class LoginService {
    private UtenteDAO utenteDAO;

    public LoginService() throws SQLException {
        this.utenteDAO = new UtenteDAO();
    }

    public LoginService(UtenteDAO utenteDAO) {
        this.utenteDAO = utenteDAO;
    }

    public Utente login(String email, String password) throws SQLException, LoginErratoException {
        Utente utente = utenteDAO.getUserByEmailPassword(email, password);
        if (utente == null) {
            throw new LoginErratoException();
        }
        return utente;
    }
}
