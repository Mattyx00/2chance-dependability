package services;

import model.beans.Categoria;
import model.beans.Prodotto;
import model.dao.CategoriaDAO;
import model.dao.ProdottoDAO;

import java.sql.SQLException;
import java.util.ArrayList;

public class InitService {
    private CategoriaDAO categoriaDAO;
    private ProdottoDAO prodottoDAO;

    public InitService() throws SQLException {
        this.categoriaDAO = new CategoriaDAO();
        this.prodottoDAO = new ProdottoDAO();
    }

    public InitService(CategoriaDAO categoriaDAO, ProdottoDAO prodottoDAO) {
        this.categoriaDAO = categoriaDAO;
        this.prodottoDAO = prodottoDAO;
    }

    public ArrayList<Categoria> getCategorie() throws SQLException {
        return categoriaDAO.getCategorie();
    }

    public ArrayList<Prodotto> getUltimiProdotti() throws SQLException {
        return prodottoDAO.getUltimiProdotti();
    }
}
