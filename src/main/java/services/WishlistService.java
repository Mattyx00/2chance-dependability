package services;

import model.beans.Prodotto;
import model.beans.Utente;
import model.beans.WishList;
import model.dao.ProdottoDAO;
import model.dao.WishListDAO;

import java.sql.SQLException;

public class WishlistService {
    private WishListDAO wishListDAO;
    private ProdottoDAO prodottoDAO;

    public WishlistService() throws SQLException {
        this.wishListDAO = new WishListDAO();
        this.prodottoDAO = new ProdottoDAO();
    }

    public WishlistService(WishListDAO wishListDAO, ProdottoDAO prodottoDAO) {
        this.wishListDAO = wishListDAO;
        this.prodottoDAO = prodottoDAO;
    }

    public void addToWishList(Utente utente, int idProdotto) throws SQLException {
        Prodotto prodotto = prodottoDAO.getProdottoById(idProdotto);
        wishListDAO.addToWishList(utente, prodotto);
    }

    public WishList getWishListByUser(Utente utente) throws SQLException {
        return wishListDAO.getWishListByUser(utente);
    }

    public void removeFromWishList(int idUtente, int idProdotto) throws SQLException {
        wishListDAO.removeFromWishList(idUtente, idProdotto);
    }
}
