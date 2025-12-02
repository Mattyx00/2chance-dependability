package services;

import model.beans.Carrello;
import model.beans.Ordine;
import model.beans.Utente;
import model.dao.OrdineDAO;

import java.sql.SQLException;
import java.util.ArrayList;

public class CheckOutService {
    private OrdineDAO ordineDAO;

    public CheckOutService() throws SQLException {
        this.ordineDAO = new OrdineDAO();
    }

    public CheckOutService(OrdineDAO ordineDAO) {
        this.ordineDAO = ordineDAO;
    }

    public void effettuaCheckout(Utente utente, Carrello carrello, String indirizzo)
            throws SQLException {

        Ordine ordine = new Ordine();
        ordine.setUtente(utente);
        ordine.setIndirizzo(indirizzo);
        ordine.setPrezzoTotale(carrello.getTotaleCarrello());
        ordine.setCarrello(carrello);

        ordineDAO.addOrdine(ordine);
    }


    public Utente aggiornaOrdiniUtente(Utente utente) throws SQLException {
        ArrayList<Ordine> ordini = ordineDAO.getOrdiniByUtente(utente);
        utente.setOrdini(ordini);
        return utente;
    }
}

