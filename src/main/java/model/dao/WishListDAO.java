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
    private Connection connection;

    public WishListDAO() throws SQLException {
        this.connection = ConPool.getConnection();
    }

    public void addToWishList(Utente u, Prodotto p) throws SQLException {
        PreparedStatement stmt = connection.prepareStatement("INSERT INTO wishlist VALUES (?, ?)");
        stmt.setInt(1, u.getId());
        stmt.setInt(2, p.getId());

        stmt.executeUpdate();

    }

    public WishList getWishListByUser(Utente u) throws SQLException {
        PreparedStatement stmt = connection.prepareStatement("SELECT * FROM wishlist WHERE id_cliente = ?");
        stmt.setInt(1, u.getId());
        WishList w = new WishList();
        w.setUtente(u);
        ArrayList<Prodotto> prodotti = new ArrayList<>();
        ResultSet rs = stmt.executeQuery();

        while(rs.next()){
            ProdottoDAO dao = new ProdottoDAO();
            Prodotto p = dao.getProdottoById(rs.getInt(2));
            prodotti.add(p);
        }

        w.setProdotti(prodotti);

        return w;
    }

    public void removeFromWishList(int id_utente, int id_prodotto) throws SQLException{
        PreparedStatement stmt = connection.prepareStatement("DELETE FROM wishlist WHERE id_cliente = ? AND id_prodotto = ?");
        stmt.setInt(1, id_utente);
        stmt.setInt(2, id_prodotto);

        stmt.executeUpdate();
    }
}
