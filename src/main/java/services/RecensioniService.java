package services;

import model.beans.Recensione;
import model.beans.Utente;
import model.dao.ProdottoDAO;
import model.dao.RecensioneDAO;
import model.dao.UtenteDAO;

import java.sql.SQLException;
import java.util.ArrayList;

public class RecensioniService {
    private RecensioneDAO recensioneDAO;
    private ProdottoDAO prodottoDAO;
    private UtenteDAO utenteDAO;

    public RecensioniService() {
        this.recensioneDAO = new RecensioneDAO();
        this.prodottoDAO = new ProdottoDAO();
        this.utenteDAO = new UtenteDAO();
    }

    public RecensioniService(RecensioneDAO recensioneDAO, ProdottoDAO prodottoDAO, UtenteDAO utenteDAO) {
        if (recensioneDAO == null) {
            throw new IllegalArgumentException("RecensioneDAO cannot be null");
        }
        if (prodottoDAO == null) {
            throw new IllegalArgumentException("ProdottoDAO cannot be null");
        }
        if (utenteDAO == null) {
            throw new IllegalArgumentException("UtenteDAO cannot be null");
        }
        this.recensioneDAO = recensioneDAO;
        this.prodottoDAO = prodottoDAO;
        this.utenteDAO = utenteDAO;
    }

    public Utente aggiungiRecensione(Utente utente, String testo, int valutazione, int idProdotto) throws SQLException {
        if (utente == null) {
            throw new IllegalArgumentException("Utente cannot be null");
        }
        if (testo == null || testo.trim().isEmpty()) {
            throw new IllegalArgumentException("Review text cannot be null or empty");
        }
        if (valutazione < 1 || valutazione > 5) {
            throw new IllegalArgumentException("Rating must be between 1 and 5");
        }
        if (idProdotto <= 0) {
            throw new IllegalArgumentException("Product ID must be positive");
        }

        model.beans.Prodotto prodotto = prodottoDAO.getProdottoById(idProdotto);
        if (prodotto == null) {
            throw new IllegalArgumentException("Product not found with ID: " + idProdotto);
        }

        Recensione r = new Recensione();
        r.setTesto(testo);
        r.setValutazione(valutazione);
        r.setUtente(utente);
        r.setProdotto(prodotto);

        recensioneDAO.addRecensione(r);

        ArrayList<Recensione> recensioni = recensioneDAO.getRecensioniByUtente(utente);
        if (recensioni == null) {
            recensioni = new ArrayList<>();
        }
        utente.setRecensioni(recensioni);
        return utente;
    }

    public Utente eliminaRecensione(int idRecensione, int idUtente) throws SQLException {
        if (idRecensione <= 0) {
            throw new IllegalArgumentException("Review ID must be positive");
        }
        if (idUtente <= 0) {
            throw new IllegalArgumentException("User ID must be positive");
        }

        recensioneDAO.deleteRecensione(idRecensione);

        Utente utente = utenteDAO.getUtenteById(idUtente);
        if (utente == null) {
            throw new IllegalArgumentException("Utente not found with ID: " + idUtente);
        }
        return utente;
    }
}
