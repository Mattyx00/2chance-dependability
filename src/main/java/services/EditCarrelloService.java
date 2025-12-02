package services;

import model.beans.Carrello;
import model.beans.Prodotto;
import model.dao.ProdottoDAO;

import java.sql.SQLException;

public class EditCarrelloService {
    private ProdottoDAO prodottoDAO;

    public EditCarrelloService() throws SQLException {
        this.prodottoDAO = new ProdottoDAO();
    }

    public EditCarrelloService(ProdottoDAO prodottoDAO) {
        this.prodottoDAO = prodottoDAO;
    }

    public Carrello eliminaProdotto(Carrello carrello, int idProdotto) throws SQLException {
        Prodotto prodotto = prodottoDAO.getProdottoById(idProdotto);
        carrello.eliminaProdotto(prodotto);
        return carrello;
    }

    public Carrello modificaQuantitaProdotto(Carrello carrello, int idProdotto, int quantita) throws SQLException {
        Prodotto prodotto = prodottoDAO.getProdottoById(idProdotto);

        carrello.cambiaQuantita(prodotto, quantita);
        return carrello;
    }
}

