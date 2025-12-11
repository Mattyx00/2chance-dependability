package services;

import model.beans.Prodotto;
import model.dao.ProdottoDAO;

import java.sql.SQLException;

public class ProdottoService {
    private final ProdottoDAO prodottoDAO;

    public ProdottoService() throws SQLException {
        this.prodottoDAO = new ProdottoDAO();
    }

    public ProdottoService(ProdottoDAO prodottoDAO) {
        if (prodottoDAO == null) {
            throw new IllegalArgumentException("ProdottoDAO cannot be null");
        }
        this.prodottoDAO = prodottoDAO;
    }

    public Prodotto getProdottoById(int id) throws SQLException {
        if (id <= 0) {
            throw new IllegalArgumentException("Product ID must be greater than 0");
        }
        return prodottoDAO.getProdottoById(id);
    }
}
