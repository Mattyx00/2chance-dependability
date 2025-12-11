package services;

import model.beans.Utente;
import model.dao.UtenteDAO;

import java.sql.SQLException;

public class UtenteService {
    private final UtenteDAO utenteDAO;

    public UtenteService() throws SQLException {
        this.utenteDAO = new UtenteDAO();
    }

    public UtenteService(UtenteDAO utenteDAO) {
        if (utenteDAO == null) {
            throw new IllegalArgumentException("UtenteDAO cannot be null");
        }
        this.utenteDAO = utenteDAO;
    }

    public Utente getUtenteById(int id) throws SQLException {
        if (id <= 0) {
            throw new IllegalArgumentException("ID must be positive");
        }
        return utenteDAO.getUtenteById(id);
    }
}
