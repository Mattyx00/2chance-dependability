package services;

import model.beans.Prodotto;
import model.beans.Utente;
import model.beans.WishList;
import model.dao.ProdottoDAO;
import model.dao.WishListDAO;

import java.sql.SQLException;

public class WishlistService {
    private final WishListDAO wishListDAO;
    private final ProdottoDAO prodottoDAO;

    public WishlistService() throws SQLException {
        this.wishListDAO = new WishListDAO();
        this.prodottoDAO = new ProdottoDAO();
    }

    public WishlistService(WishListDAO wishListDAO, ProdottoDAO prodottoDAO) {
        if (wishListDAO == null) {
            throw new IllegalArgumentException("WishListDAO cannot be null");
        }
        if (prodottoDAO == null) {
            throw new IllegalArgumentException("ProdottoDAO cannot be null");
        }
        this.wishListDAO = wishListDAO;
        this.prodottoDAO = prodottoDAO;
    }

    public void addToWishList(Utente utente, int idProdotto) throws SQLException {
        if (utente == null) {
            throw new IllegalArgumentException("Utente cannot be null");
        }
        if (idProdotto <= 0) {
            throw new IllegalArgumentException("Product ID must be positive: " + idProdotto);
        }

        Prodotto prodotto = prodottoDAO.getProdottoById(idProdotto);
        if (prodotto == null) {
            throw new IllegalArgumentException("Product not found with ID: " + idProdotto);
        }

        wishListDAO.addToWishList(utente, prodotto);
    }

    public WishList getWishListByUser(Utente utente) throws SQLException {
        if (utente == null) {
            throw new IllegalArgumentException("Utente cannot be null");
        }
        return wishListDAO.getWishListByUser(utente);
    }

    public void removeFromWishList(int idUtente, int idProdotto) throws SQLException {
        if (idUtente <= 0) {
            throw new IllegalArgumentException("User ID must be positive: " + idUtente);
        }
        if (idProdotto <= 0) {
            throw new IllegalArgumentException("Product ID must be positive: " + idProdotto);
        }
        wishListDAO.removeFromWishList(idUtente, idProdotto);
    }
}
