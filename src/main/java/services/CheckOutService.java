package services;

import model.beans.Carrello;
import model.beans.Ordine;
import model.beans.Utente;
import model.dao.OrdineDAO;

import java.sql.SQLException;
import java.util.ArrayList;

public class CheckOutService {

    public void effettuaCheckout(Utente utente, Carrello carrello, String indirizzo)
            throws SQLException {

        OrdineDAO dao = new OrdineDAO();

        Ordine ordine = new Ordine();
        ordine.setUtente(utente);
        ordine.setIndirizzo(indirizzo);
        ordine.setPrezzoTotale(carrello.getTotaleCarrello());
        ordine.setCarrello(carrello);

        dao.addOrdine(ordine);
    }


    public Utente aggiornaOrdiniUtente(Utente utente) throws SQLException {
        OrdineDAO dao = new OrdineDAO();
        ArrayList<Ordine> ordini = dao.getOrdiniByUtente(utente);
        utente.setOrdini(ordini);
        return utente;
    }
}
