package services;

import model.beans.Prodotto;
import model.dao.ProdottoDAO;

import java.sql.SQLException;
import java.util.ArrayList;

public class ProdottiPerCategoriaService {
    private ProdottoDAO prodottoDAO;

    public ProdottiPerCategoriaService() throws SQLException {
        this.prodottoDAO = new ProdottoDAO();
    }

    public ProdottiPerCategoriaService(ProdottoDAO prodottoDAO) {
        this.prodottoDAO = prodottoDAO;
    }

    public ArrayList<Prodotto> getProdottiByCategoria(String categoria) throws SQLException {
        return prodottoDAO.getProdottiByCategoria(categoria);
    }
}
