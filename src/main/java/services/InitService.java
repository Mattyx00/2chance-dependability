package services;

import model.beans.Categoria;
import model.beans.Prodotto;
import model.dao.CategoriaDAO;
import model.dao.ProdottoDAO;

import java.sql.SQLException;
import java.util.ArrayList;

public class InitService {
    private final CategoriaDAO categoriaDAO;
    private final ProdottoDAO prodottoDAO;

    public InitService() throws SQLException {
        this.categoriaDAO = new CategoriaDAO();
        this.prodottoDAO = new ProdottoDAO();
    }

    public InitService(CategoriaDAO categoriaDAO, ProdottoDAO prodottoDAO) {
        if (categoriaDAO == null) {
            throw new IllegalArgumentException("CategoriaDAO cannot be null");
        }
        if (prodottoDAO == null) {
            throw new IllegalArgumentException("ProdottoDAO cannot be null");
        }
        this.categoriaDAO = categoriaDAO;
        this.prodottoDAO = prodottoDAO;
    }

    public ArrayList<Categoria> getCategorie() throws SQLException {
        ArrayList<Categoria> categorie = categoriaDAO.getCategorie();
        return categorie != null ? categorie : new ArrayList<>();
    }

    public ArrayList<Prodotto> getUltimiProdotti() throws SQLException {
        ArrayList<Prodotto> prodotti = prodottoDAO.getUltimiProdotti();
        return prodotti != null ? prodotti : new ArrayList<>();
    }
}
