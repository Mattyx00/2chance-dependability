package services;

import model.beans.Carrello;
import model.beans.Prodotto;
import model.beans.ProdottoCarrello;
import model.dao.ProdottoDAO;

import java.sql.SQLException;

public class AggiungiCarrelloService {

    public Carrello aggiungiAlCarrello(Carrello carrello, int idProdotto, int quantita)
            throws SQLException {

        // Recupera o crea un nuovo carrello

        if (carrello == null) {
            carrello = new Carrello();
        }

        // Recupero del prodotto dal DB
        ProdottoDAO dao = new ProdottoDAO();
        Prodotto prodotto = dao.getProdottoById(idProdotto);

        // Aggiorno il carrello
        boolean trovato = false;

        for (ProdottoCarrello pc : carrello.getProdotti()) {
            if (pc.getProdotto().getId() == prodotto.getId()) {
                pc.setQuantita(pc.getQuantita() + quantita);
                trovato = true;
                break;
            }
        }

        if (!trovato) {
            ProdottoCarrello nuovo = new ProdottoCarrello();
            nuovo.setProdotto(prodotto);
            nuovo.setQuantita(quantita);
            carrello.aggiungiProdotto(nuovo);
        }

        return carrello;
    }
}
