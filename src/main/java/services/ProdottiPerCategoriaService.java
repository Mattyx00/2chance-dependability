package services;

import model.beans.Prodotto;
import model.dao.ProdottoDAO;

import java.sql.SQLException;
import java.util.ArrayList;

public class ProdottiPerCategoriaService {
    private final ProdottoDAO prodottoDAO;

    /**
     * Default constructor.
     * Initializes the service with a default ProdottoDAO.
     *
     * @throws SQLException if ProdottoDAO initialization fails.
     */
    public ProdottiPerCategoriaService() throws SQLException {
        this.prodottoDAO = new ProdottoDAO();
    }

    /**
     * Parameterized constructor for dependency injection.
     *
     * @param prodottoDAO the ProdottoDAO to use, must not be null.
     */
    public ProdottiPerCategoriaService(ProdottoDAO prodottoDAO) {
        if (prodottoDAO == null) {
            throw new IllegalArgumentException("ProdottoDAO cannot be null");
        }
        this.prodottoDAO = prodottoDAO;
    }

    /**
     * Retrieves products by category.
     *
     * @param categoria the category name, must not be null or empty.
     * @return a list of products in the specified category.
     * @throws SQLException             if a database error occurs.
     * @throws IllegalArgumentException if the category is invalid.
     * @throws IllegalStateException    if the service is not properly initialized.
     */
    public ArrayList<Prodotto> getProdottiByCategoria(String categoria) throws SQLException {
        if (categoria == null || categoria.trim().isEmpty()) {
            throw new IllegalArgumentException("Category name cannot be null or empty");
        }
        if (prodottoDAO == null) {
            // This should technically not happen due to constructor checks,
            // but is added for defensive depth if fields are mutable or reflection is used.
            // Since I made the field final, this is strictly unreachable code unless
            // the object was created in a very weird way, but adhering to the prompt's
            // "catch invalid logical states immediately".
            throw new IllegalStateException("Service is not properly initialized: ProdottoDAO is null");
        }
        return prodottoDAO.getProdottiByCategoria(categoria);
    }
}
