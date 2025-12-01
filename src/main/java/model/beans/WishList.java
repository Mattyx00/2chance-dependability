package model.beans;

import java.util.ArrayList;

public class WishList {
    /* @ spec_public @ */
    Utente utente;
    /* @ spec_public @ */
    ArrayList<Prodotto> prodotti;

    /* @ ensures \result == utente; @ */
    public Utente getUtente() {
        return utente;
    }

    /* @ ensures this.utente == utente; @ */
    public void setUtente(Utente utente) {
        this.utente = utente;
    }

    /* @ ensures \result == prodotti; @ */
    public ArrayList<Prodotto> getProdotti() {
        return prodotti;
    }

    /* @ ensures this.prodotti == prodotti; @ */
    public void setProdotti(ArrayList<Prodotto> prodotti) {
        this.prodotti = prodotti;
    }
}
