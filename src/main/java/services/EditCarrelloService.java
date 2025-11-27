package services;

import model.beans.Carrello;
import model.beans.Prodotto;
import model.dao.ProdottoDAO;

import java.sql.SQLException;

public class EditCarrelloService {
    public Carrello eliminaProdotto(Carrello carrello, int idProdotto) throws SQLException {
        ProdottoDAO dao = new ProdottoDAO();
        Prodotto prodotto = dao.getProdottoById(idProdotto);
        carrello.eliminaProdotto(prodotto);
        return carrello;
    }

    public Carrello modificaQuantitaProdotto(Carrello carrello, int idProdotto, int quantita) throws SQLException {
        ProdottoDAO dao = new ProdottoDAO();
        Prodotto prodotto = dao.getProdottoById(idProdotto);

        carrello.cambiaQuantita(prodotto, quantita);
        return carrello;
    }
}
