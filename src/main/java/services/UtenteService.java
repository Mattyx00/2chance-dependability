package services;

import model.beans.Utente;
import model.dao.UtenteDAO;

import java.sql.SQLException;

public class UtenteService {
    private UtenteDAO utenteDAO;

    public UtenteService() throws SQLException {
        this.utenteDAO = new UtenteDAO();
    }

    public UtenteService(UtenteDAO utenteDAO) {
        this.utenteDAO = utenteDAO;
    }

    public Utente getUtenteById(int id) throws SQLException {
        return utenteDAO.getUtenteById(id);
    }
}
