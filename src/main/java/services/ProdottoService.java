package services;

import model.beans.Prodotto;
import model.dao.ProdottoDAO;

import java.sql.SQLException;

public class ProdottoService {
    private ProdottoDAO prodottoDAO;

    public ProdottoService() throws SQLException {
        this.prodottoDAO = new ProdottoDAO();
    }

    public ProdottoService(ProdottoDAO prodottoDAO) {
        this.prodottoDAO = prodottoDAO;
    }

    public Prodotto getProdottoById(int id) throws SQLException {
        return prodottoDAO.getProdottoById(id);
    }
}
