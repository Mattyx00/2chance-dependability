package model.beans;

import java.util.ArrayList;

public class WishList {
    private Utente utente;
    private ArrayList<Prodotto> prodotti;


    public WishList() {
        prodotti = new ArrayList<>();
    }

    public WishList(Utente utente) {
        if (utente == null) {
            throw new IllegalArgumentException("L'utente non può essere null");
        }
        this.utente = utente;
        this.prodotti = new ArrayList<>();
    }

    public Utente getUtente() {
        return utente;
    }

    public void setUtente(Utente utente) {
        if (utente == null) {
            throw new IllegalArgumentException("L'utente non può essere null");
        }
        this.utente = utente;
    }

    public ArrayList<Prodotto> getProdotti() {
        return prodotti;
    }

    public void setProdotti(ArrayList<Prodotto> prodotti) {
        if (prodotti == null) {
            throw new IllegalArgumentException("La lista dei prodotti non può essere null");
        }
        this.prodotti = prodotti;
    }
}
