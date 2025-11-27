package services;

import model.beans.Prodotto;
import model.dao.ProdottoDAO;

import java.sql.SQLException;

public class ConfrontaService {

    public Prodotto[] confrontaProdotti(int id1, int id2) throws SQLException {
        ProdottoDAO dao = new ProdottoDAO();

        Prodotto p1 = dao.getProdottoById(id1);
        Prodotto p2 = dao.getProdottoById(id2);

        return new Prodotto[]{p1, p2};
    }
}
