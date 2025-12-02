package services;

import model.beans.Prodotto;
import model.dao.ProdottoDAO;

import java.sql.SQLException;

public class ConfrontaService {
    private ProdottoDAO prodottoDAO;

    public ConfrontaService() throws SQLException {
        this.prodottoDAO = new ProdottoDAO();
    }

    public ConfrontaService(ProdottoDAO prodottoDAO) {
        this.prodottoDAO = prodottoDAO;
    }

    public Prodotto[] confrontaProdotti(int id1, int id2) throws SQLException {
        Prodotto p1 = prodottoDAO.getProdottoById(id1);
        Prodotto p2 = prodottoDAO.getProdottoById(id2);

        return new Prodotto[]{p1, p2};
    }
}

