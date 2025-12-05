package model.dao;

import model.beans.Prodotto;
import model.beans.Utente;
import model.beans.WishList;
import utils.ConPool;

import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.util.ArrayList;

public class WishListDAO {

    public WishListDAO() {
    }

    public void addToWishList(Utente u, Prodotto p) throws SQLException {
        if (u == null) {
            throw new IllegalArgumentException("L'utente non può essere null");
        }
        if (p == null) {
            throw new IllegalArgumentException("Il prodotto non può essere null");
        }
        try (Connection connection = ConPool.getConnection();
                PreparedStatement stmt = connection.prepareStatement("INSERT INTO wishlist VALUES (?, ?)")) {
            stmt.setInt(1, u.getId());
            stmt.setInt(2, p.getId());

            stmt.executeUpdate();
        }

    }

    public WishList getWishListByUser(Utente u) throws SQLException {
        if (u == null) {
            throw new IllegalArgumentException("L'utente non può essere null");
        }
        try (Connection connection = ConPool.getConnection();
                PreparedStatement stmt = connection.prepareStatement("SELECT * FROM wishlist WHERE id_cliente = ?")) {
            stmt.setInt(1, u.getId());
            WishList w = new WishList();
            w.setUtente(u);
            ArrayList<Prodotto> prodotti = new ArrayList<>();
            ResultSet rs = stmt.executeQuery();

            while (rs.next()) {
                ProdottoDAO dao = new ProdottoDAO();
                Prodotto p = dao.getProdottoById(rs.getInt(2));
                prodotti.add(p);
            }

            w.setProdotti(prodotti);

            return w;
        }
    }

    public void removeFromWishList(int id_utente, int id_prodotto) throws SQLException {
        if (id_utente <= 0) {
            throw new IllegalArgumentException("L'ID dell'utente deve essere maggiore di zero");
        }
        if (id_prodotto <= 0) {
            throw new IllegalArgumentException("L'ID del prodotto deve essere maggiore di zero");
        }
        try (Connection connection = ConPool.getConnection();
                PreparedStatement stmt = connection
                        .prepareStatement("DELETE FROM wishlist WHERE id_cliente = ? AND id_prodotto = ?")) {
            stmt.setInt(1, id_utente);
            stmt.setInt(2, id_prodotto);

            stmt.executeUpdate();
        }
    }
}
