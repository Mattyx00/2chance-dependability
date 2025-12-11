package services;

import model.beans.Prodotto;
import model.dao.ProdottoDAO;

import java.sql.SQLException;
import java.util.ArrayList;

public class RicercaService {
    private final ProdottoDAO prodottoDAO;

    public RicercaService() throws SQLException {
        this.prodottoDAO = new ProdottoDAO();
    }

    public RicercaService(ProdottoDAO prodottoDAO) {
        if (prodottoDAO == null) {
            throw new IllegalArgumentException("ProdottoDAO cannot be null");
        }
        this.prodottoDAO = prodottoDAO;
    }

    public ArrayList<Prodotto> cercaProdotti(String query) throws SQLException {
        if (query == null || query.trim().isEmpty()) {
            throw new IllegalArgumentException("Query string cannot be null or empty");
        }
        return prodottoDAO.cercaProdotti(query);
    }
}
