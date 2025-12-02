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

    public RecensioniService() throws SQLException {
        this.recensioneDAO = new RecensioneDAO();
        this.prodottoDAO = new ProdottoDAO();
        this.utenteDAO = new UtenteDAO();
    }

    public RecensioniService(RecensioneDAO recensioneDAO, ProdottoDAO prodottoDAO, UtenteDAO utenteDAO) {
        this.recensioneDAO = recensioneDAO;
        this.prodottoDAO = prodottoDAO;
        this.utenteDAO = utenteDAO;
    }

    public Utente aggiungiRecensione(Utente utente, String testo, int valutazione, int idProdotto) throws SQLException {
        Recensione r = new Recensione();
        r.setTesto(testo);
        r.setValutazione(valutazione);
        r.setUtente(utente);
        r.setProdotto(prodottoDAO.getProdottoById(idProdotto));
        recensioneDAO.addRecensione(r);

        ArrayList<Recensione> recensioni = recensioneDAO.getRecensioniByUtente(utente);
        utente.setRecensioni(recensioni);
        return utente;
    }

    public Utente eliminaRecensione(int idRecensione, int idUtente) throws SQLException {
        recensioneDAO.deleteRecensione(idRecensione);
        return utenteDAO.getUtenteById(idUtente);
    }
}
