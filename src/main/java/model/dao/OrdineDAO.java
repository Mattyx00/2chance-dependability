package model.dao;

import model.beans.*;
import utils.ConPool;

import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.util.ArrayList;

public class OrdineDAO {
    private Connection connection;

    public OrdineDAO() throws SQLException {
        this.connection = ConPool.getConnection();
    }

    public Ordine getOrdineById(int id) throws SQLException {
        PreparedStatement stmt = connection.prepareStatement("SELECT * FROM ordine WHERE id_ordine = ?");
        stmt.setInt(1, id);
        ResultSet rs = stmt.executeQuery();

        Ordine risultato = new Ordine();
        if(rs.next()){
            risultato.setId(id);
            Utente utente = new Utente();
            utente.setId(rs.getInt(2));
            risultato.setUtente(utente);
            risultato.setDataOrdine(rs.getDate(2));
            risultato.setIndirizzo(rs.getString(4));
            risultato.setPrezzoTotale(rs.getDouble(5));

        }

        return risultato;
    }

    public Carrello getProdottoOrdine(Ordine o) throws SQLException {
        PreparedStatement stmt = connection.prepareStatement("SELECT * FROM composto c, ordine o, prodotto p where c.id_ordine = o.id_ordine and c.id_prodotto = p.id_prodotto and o.id_ordine = ?");
        stmt.setInt(1, o.getId());
        ResultSet rs = stmt.executeQuery();
        Carrello c = new Carrello();

        while(rs.next()){
            ProdottoCarrello p = new ProdottoCarrello();
            p.setQuantita(rs.getInt(3));

            Prodotto prod = new Prodotto();
            prod.setMarca(rs.getString(17));
            prod.setModello(rs.getString(18));
            prod.setId(rs.getInt(2));
            prod.setImmagine(rs.getString(16));
            prod.setPrezzo(rs.getDouble(4));
            p.setProdotto(prod);
            c.aggiungiProdotto(p);
        }

        return c;

    }


    public ArrayList<Ordine> getOrdiniByUtente(Utente utente) throws SQLException {
        PreparedStatement stmt = connection.prepareStatement("SELECT * FROM ordine WHERE id_utente = ?;");
        stmt.setInt(1, utente.getId());
        ResultSet rs = stmt.executeQuery();
        ArrayList<Ordine> ordini = new ArrayList<>();

        while(rs.next()){
            Ordine ordine = new Ordine();
            ordine.setId(rs.getInt(1));
            Utente utenteProvv = new Utente();
            utenteProvv.setId(rs.getInt(2));
            ordine.setUtente(utenteProvv);
            ordine.setDataOrdine(rs.getDate(3));
            ordine.setIndirizzo(rs.getString(4));
            ordine.setPrezzoTotale(rs.getDouble(5));
            Carrello carrello = getProdottoOrdine(ordine);
            ordine.setCarrello(carrello);
            ordini.add(ordine);
        }
        return ordini;
    }

    public void addOrdine(Ordine ordine) throws SQLException {
        PreparedStatement stmt = connection.prepareStatement("INSERT INTO ordine VALUES (default, ?, default, ?, ?)");

        stmt.setInt(1,ordine.getUtente().getId());
        stmt.setString(2, ordine.getIndirizzo());
        stmt.setDouble(3, ordine.getPrezzoTotale());
        stmt.executeUpdate();

        PreparedStatement stmt2 = connection.prepareStatement("INSERT INTO composto VALUES(?, ?, ?, ?)"); //idOrdine, idProdotto, QtàOrdinata, PrezzoUnitario

        ResultSet rs = connection.prepareStatement("SELECT * FROM ordine ORDER BY id_ordine desc").executeQuery();
        rs.first();
        int id_ordine = rs.getInt(1);


        for(ProdottoCarrello e: ordine.getCarrello().getProdotti()){
            stmt2.setInt(1,id_ordine);
            stmt2.setInt(2, e.getProdotto().getId());
            stmt2.setInt(3, e.getQuantita());
            stmt2.setDouble(4, e.getProdotto().getPrezzo());
            stmt2.executeUpdate();

        }

        }

        public ArrayList<Ordine> getOrdini() throws SQLException {
            PreparedStatement stmt = connection.prepareStatement("SELECT * FROM ordine");
            ResultSet rs = stmt.executeQuery();
            ArrayList<Ordine> ordini = new ArrayList<>();
            while(rs.next()){
                Ordine o = new Ordine();
                o.setId(rs.getInt(1));
                UtenteDAO dao = new UtenteDAO();
                Utente u = new Utente();
                u.setId(rs.getInt(2));
                o.setUtente(u);
                o.setDataOrdine(rs.getDate(3));
                o.setIndirizzo(rs.getString(4));
                o.setPrezzoTotale(rs.getDouble(5));
                ordini.add(o);
            }
            return ordini;
        }
}
