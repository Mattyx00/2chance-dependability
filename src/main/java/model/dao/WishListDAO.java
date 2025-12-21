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
import java.util.logging.Logger;

public class WishListDAO {

    private static final Logger LOGGER = Logger.getLogger(WishListDAO.class.getName());

    public WishListDAO() {
    }

    /**
     * Adds a product to the user's wishlist.
     *
     * @param u the user, must not be null and must have a valid ID > 0
     * @param p the product, must not be null and must have a valid ID > 0
     * @throws IllegalArgumentException if u or p is null, or if IDs are invalid
     * @throws SQLException             if a database access error occurs
     */
    public void addToWishList(Utente u, Prodotto p) throws SQLException {
        // Validate utente
        if (u == null) {
            throw new IllegalArgumentException("L'utente non può essere null.");
        }
        if (u.getId() <= 0) {
            throw new IllegalArgumentException("L'ID dell'utente deve essere maggiore di zero.");
        }

        // Validate prodotto
        if (p == null) {
            throw new IllegalArgumentException("Il prodotto non può essere null.");
        }
        if (p.getId() <= 0) {
            throw new IllegalArgumentException("L'ID del prodotto deve essere maggiore di zero.");
        }

        try (Connection connection = ConPool.getConnection();
                PreparedStatement stmt = connection.prepareStatement("INSERT INTO wishlist VALUES (?, ?)")) {
            stmt.setInt(1, u.getId());
            stmt.setInt(2, p.getId());

            stmt.executeUpdate();
            LOGGER.info("Added product " + p.getId() + " to wishlist for user " + u.getId());
        } catch (SQLException e) {
            LOGGER.warning("Failed to add product to wishlist: " + e.getMessage());
            throw e;
        }
    }

    /**
     * Retrieves the wishlist for a given user, including all products.
     *
     * @param u the user, must not be null and must have a valid ID > 0
     * @return a WishList containing the user's products (never null, but may be
     *         empty)
     * @throws IllegalArgumentException if u is null or has an invalid ID
     * @throws SQLException             if a database access error occurs
     */
    public WishList getWishListByUser(Utente u) throws SQLException {
        // Validate utente
        if (u == null) {
            throw new IllegalArgumentException("L'utente non può essere null.");
        }
        if (u.getId() <= 0) {
            throw new IllegalArgumentException("L'ID dell'utente deve essere maggiore di zero.");
        }

        try (Connection connection = ConPool.getConnection();
                PreparedStatement stmt = connection.prepareStatement("SELECT * FROM wishlist WHERE id_cliente = ?")) {
            stmt.setInt(1, u.getId());

            WishList w = new WishList();
            w.setUtente(u);
            ArrayList<Prodotto> prodotti = new ArrayList<>();

            try (ResultSet rs = stmt.executeQuery()) {
                ProdottoDAO dao = getProdottoDAO();

                while (rs.next()) {
                    int productId = rs.getInt(2);
                    if (productId <= 0) {
                        LOGGER.warning("Invalid product ID " + productId + " in wishlist for user " + u.getId());
                        continue; // Skip invalid entries
                    }

                    try {
                        Prodotto p = dao.getProdottoById(productId);
                        if (p != null) {
                            prodotti.add(p);
                        } else {
                            LOGGER.warning("Product " + productId + " not found for wishlist of user " + u.getId());
                        }
                    } catch (SQLException e) {
                        LOGGER.warning("Failed to load product " + productId + " for user " + u.getId() + ": "
                                + e.getMessage());
                        // Continue loading other products instead of failing completely
                    }
                }
            }

            w.setProdotti(prodotti);
            return w;
        }
    }

    /**
     * Removes a product from a user's wishlist.
     *
     * @param id_utente   the user ID, must be > 0
     * @param id_prodotto the product ID, must be > 0
     * @throws IllegalArgumentException if either ID is <= 0
     * @throws SQLException             if a database access error occurs
     */
    public void removeFromWishList(int id_utente, int id_prodotto) throws SQLException {
        if (id_utente <= 0) {
            throw new IllegalArgumentException("L'ID dell'utente deve essere maggiore di zero.");
        }
        if (id_prodotto <= 0) {
            throw new IllegalArgumentException("L'ID del prodotto deve essere maggiore di zero.");
        }

        try (Connection connection = ConPool.getConnection();
                PreparedStatement stmt = connection
                        .prepareStatement("DELETE FROM wishlist WHERE id_cliente = ? AND id_prodotto = ?")) {
            stmt.setInt(1, id_utente);
            stmt.setInt(2, id_prodotto);

            int rowsAffected = stmt.executeUpdate();
            if (rowsAffected > 0) {
                LOGGER.info("Removed product " + id_prodotto + " from wishlist for user " + id_utente);
            } else {
                LOGGER.info("No wishlist entry found for user " + id_utente + " and product " + id_prodotto);
            }
        } catch (SQLException e) {
            LOGGER.warning("Failed to remove product from wishlist: " + e.getMessage());
            throw e;
        }
    }

    /**
     * Protected factory method for ProdottoDAO to enable testability.
     *
     * @return a new ProdottoDAO instance
     */
    protected ProdottoDAO getProdottoDAO() {
        return new ProdottoDAO();
    }
}
