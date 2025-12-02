package model.dao;

import model.beans.Categoria;
import model.beans.Prodotto;
import model.beans.Recensione;
import model.beans.Utente;
import utils.ConPool;

import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.util.ArrayList;

public class RecensioneDAO {

    public RecensioneDAO() {
    }


    public ArrayList<Recensione> getRecensioniByUtente(Utente utente) throws SQLException {
        try (Connection connection = ConPool.getConnection();
             PreparedStatement stmt = connection.prepareStatement("SELECT * FROM recensione, utente, prodotto WHERE recensione.cliente = ? AND recensione.cliente = utente.id_utente AND recensione.prodotto = prodotto.id_prodotto")) {
            stmt.setInt(1, utente.getId());
            ResultSet rs = stmt.executeQuery();
            ArrayList<Recensione> recensioni = new ArrayList<>();

            while(rs.next()){
                Recensione recensione = new Recensione();
                recensione.setId(rs.getInt(1));
                Utente utenteProvvisorio = new Utente();
                utenteProvvisorio.setId(rs.getInt(2));
                utenteProvvisorio.setNome(rs.getString(8));
                utenteProvvisorio.setCognome(rs.getString(9));
                utenteProvvisorio.setAdmin(rs.getBoolean(10));
                utenteProvvisorio.setEmail(rs.getString(11));
                utenteProvvisorio.setTelefono(rs.getString(12));
                utenteProvvisorio.setPassword(rs.getString(13));
                utenteProvvisorio.setImmagine(rs.getString(14));
                recensione.setUtente(utenteProvvisorio);
                Prodotto prodotto = new Prodotto();
                prodotto.setId(rs.getInt(3));
                Categoria categoria = new Categoria();
                categoria.setNomeCategoria(rs.getString(16));
                prodotto.setCategoria(categoria);
                prodotto.setDescrizione(rs.getString(17));
                prodotto.setDimensioni(rs.getString(18));
                prodotto.setQuantitaProdotto(rs.getInt(19));
                prodotto.setPeso(rs.getInt(20));
                prodotto.setImmagine(rs.getString(21));
                prodotto.setMarca(rs.getString(22));
                prodotto.setModello(rs.getString(23));
                prodotto.setPrezzo(rs.getDouble(24));
                recensione.setProdotto(prodotto);
                recensione.setDataRecensione(rs.getDate(4));
                recensione.setTesto(rs.getString(5));
                recensione.setValutazione(rs.getInt(6));
                recensioni.add(recensione);
            }

            return recensioni;
        }
    }

    public ArrayList<Recensione> getRecensioniByProdotto(Prodotto prodotto) throws SQLException {
        try (Connection connection = ConPool.getConnection();
             PreparedStatement stmt = connection.prepareStatement("SELECT * FROM recensione, utente, prodotto WHERE recensione.prodotto = ? AND recensione.cliente = utente.id_utente AND recensione.prodotto = prodotto.id_prodotto")) {
            stmt.setInt(1, prodotto.getId());
            ResultSet rs = stmt.executeQuery();
            ArrayList<Recensione> recensioni = new ArrayList<>();

            while(rs.next()){
                Recensione recensione = new Recensione();
                recensione.setId(rs.getInt(1));
                Utente utenteProvvisorio = new Utente();
                utenteProvvisorio.setId(rs.getInt(2));
                utenteProvvisorio.setNome(rs.getString(8));
                utenteProvvisorio.setCognome(rs.getString(9));
                utenteProvvisorio.setAdmin(rs.getBoolean(10));
                utenteProvvisorio.setEmail(rs.getString(11));
                utenteProvvisorio.setTelefono(rs.getString(12));
                utenteProvvisorio.setPassword(rs.getString(13));
                utenteProvvisorio.setImmagine(rs.getString(14));
                recensione.setUtente(utenteProvvisorio);
                Prodotto prodottoProvvisorio = new Prodotto();
                prodottoProvvisorio.setId(rs.getInt(3));
                Categoria categoria = new Categoria();
                categoria.setNomeCategoria(rs.getString(16));
                prodottoProvvisorio.setCategoria(categoria);
                prodottoProvvisorio.setDescrizione(rs.getString(17));
                prodottoProvvisorio.setDimensioni(rs.getString(18));
                prodottoProvvisorio.setQuantitaProdotto(rs.getInt(19));
                prodottoProvvisorio.setPeso(rs.getInt(20));
                prodottoProvvisorio.setImmagine(rs.getString(21));
                prodottoProvvisorio.setMarca(rs.getString(22));
                prodottoProvvisorio.setModello(rs.getString(23));
                prodottoProvvisorio.setPrezzo(rs.getDouble(24));
                recensione.setProdotto(prodottoProvvisorio);
                recensione.setDataRecensione(rs.getDate(4));
                recensione.setTesto(rs.getString(5));
                recensione.setValutazione(rs.getInt(6));
                recensioni.add(recensione);
            }

            return recensioni;
        }
    }


    public int addRecensione (Recensione recensione) throws SQLException{
        try (Connection connection = ConPool.getConnection();
             PreparedStatement stmt = connection.prepareStatement("INSERT INTO recensione VALUES (default, ?, ?, default, ?, ?);")) {
            System.out.println(recensione.getUtente().getId());
            stmt.setInt(1, recensione.getUtente().getId());
            stmt.setInt(2, recensione.getProdotto().getId());
            stmt.setString(3, recensione.getTesto());
            stmt.setInt(4, recensione.getValutazione());
            return stmt.executeUpdate();
        }
    }

    public void deleteRecensione(int id_recensione) throws SQLException {
        try (Connection connection = ConPool.getConnection();
             PreparedStatement stmt = connection.prepareStatement("DELETE FROM recensione WHERE id_recensione = ?")) {
            stmt.setInt(1, id_recensione);

            stmt.executeUpdate();
        }
    }


}
