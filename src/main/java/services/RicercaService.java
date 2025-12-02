package services;

import model.beans.Prodotto;
import model.dao.ProdottoDAO;

import java.sql.SQLException;
import java.util.ArrayList;

public class RicercaService {
    private ProdottoDAO prodottoDAO;

    public RicercaService() throws SQLException {
        this.prodottoDAO = new ProdottoDAO();
    }

    public RicercaService(ProdottoDAO prodottoDAO) {
        this.prodottoDAO = prodottoDAO;
    }

    public ArrayList<Prodotto> cercaProdotti(String query) throws SQLException {
        return prodottoDAO.cercaProdotti(query);
    }
}
