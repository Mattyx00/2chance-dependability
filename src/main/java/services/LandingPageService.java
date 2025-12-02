package services;

import model.beans.Prodotto;
import model.dao.ProdottoDAO;

import java.sql.SQLException;
import java.util.ArrayList;

public class LandingPageService {
    private ProdottoDAO prodottoDAO;

    public LandingPageService() throws SQLException {
        this.prodottoDAO = new ProdottoDAO();
    }

    public LandingPageService(ProdottoDAO prodottoDAO) {
        this.prodottoDAO = prodottoDAO;
    }

    public ArrayList<Prodotto> getUltimiProdotti() throws SQLException {
        return prodottoDAO.getUltimiProdotti();
    }
}
