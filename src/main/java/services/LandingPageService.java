package services;

import model.beans.Prodotto;
import model.dao.ProdottoDAO;

import java.sql.SQLException;
import java.util.ArrayList;

public class LandingPageService {
    private final ProdottoDAO prodottoDAO;

    public LandingPageService() throws SQLException {
        this(new ProdottoDAO());
    }

    public LandingPageService(ProdottoDAO prodottoDAO) {
        if (prodottoDAO == null) {
            throw new IllegalArgumentException("ProdottoDAO cannot be null");
        }
        this.prodottoDAO = prodottoDAO;
    }

    public ArrayList<Prodotto> getUltimiProdotti() throws SQLException {
        ArrayList<Prodotto> prodotti = prodottoDAO.getUltimiProdotti();
        return prodotti != null ? prodotti : new ArrayList<>();
    }
}
