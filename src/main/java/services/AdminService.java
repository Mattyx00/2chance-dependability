package services;

import model.beans.*;
import model.dao.CategoriaDAO;
import model.dao.OrdineDAO;
import model.dao.ProdottoDAO;
import model.dao.UtenteDAO;
import org.json.JSONArray;
import org.json.JSONObject;

import javax.servlet.http.Part;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.sql.SQLException;
import java.util.ArrayList;

public class AdminService {
    private ProdottoDAO prodottoDAO;
    private CategoriaDAO categoriaDAO;
    private UtenteDAO utenteDAO;
    private OrdineDAO ordineDAO;

    /*@
      @ public normal_behavior
      @   ensures prodottoDAO != null;
      @   ensures categoriaDAO != null;
      @   ensures utenteDAO != null;
      @   ensures ordineDAO != null;
      @   signals (SQLException e) true;
      @*/
    public AdminService() throws SQLException {
        this.prodottoDAO = new ProdottoDAO();
        this.categoriaDAO = new CategoriaDAO();
        this.utenteDAO = new UtenteDAO();
        this.ordineDAO = new OrdineDAO();
    }

    /*@
      @ public normal_behavior
      @   requires prodottoDAO != null;
      @   requires categoriaDAO != null;
      @   requires utenteDAO != null;
      @   requires ordineDAO != null;
      @   ensures this.prodottoDAO == prodottoDAO;
      @   ensures this.categoriaDAO == categoriaDAO;
      @   ensures this.utenteDAO == utenteDAO;
      @   ensures this.ordineDAO == ordineDAO;
      @*/
    public AdminService(ProdottoDAO prodottoDAO, CategoriaDAO categoriaDAO, UtenteDAO utenteDAO, OrdineDAO ordineDAO) {
        this.prodottoDAO = prodottoDAO;
        this.categoriaDAO = categoriaDAO;
        this.utenteDAO = utenteDAO;
        this.ordineDAO = ordineDAO;
    }

    /*@
      @ public normal_behavior
      @   requires p != null;
      @   requires categoria != null;
      @   requires immagine != null;
      @   requires specifiche != null;
      @   signals (IOException e) true;
      @   signals (SQLException e) true;
      @*/
    public void aggiungiProdotto(Prodotto p, Categoria categoria, Part immagine, String specifiche) throws IOException, SQLException {
        p.setCategoria(categoria);
        String fileName = Paths.get(immagine.getSubmittedFileName()).getFileName().toString();
        p.setImmagine(fileName);
        prodottoDAO.addProdotto(p);

        try (InputStream fileStream = immagine.getInputStream()) {
            String currentDirectory = System.getProperty("user.dir");
            Path uploadPath = Paths.get(currentDirectory).getParent().resolve("upload");
            Files.createDirectories(uploadPath);
            File file = new File(uploadPath + File.separator + fileName);
            if (!file.exists())
                Files.copy(fileStream, file.toPath());
        }

        // Specifiche prodotto
        JSONObject obj = new JSONObject(specifiche);
        JSONArray array = obj.getJSONArray("specifiche");
        ArrayList<Specifiche> list = new ArrayList<>();

        for (int i = 0; i < array.length(); i++) {
            Specifiche s = new Specifiche();
            s.setNome(array.getJSONObject(i).getString("nome"));
            s.setValore(array.getJSONObject(i).getString("valore"));
            list.add(s);
        }

        prodottoDAO.aggiungiSpecifiche(list, prodottoDAO.getLastProduct());
    }

    /*@
      @ public normal_behavior
      @   ensures \result != null;
      @   signals (IOException e) true;
      @   signals (SQLException e) true;
      @*/
    public String mostraProdotti() throws IOException, SQLException {
        /*Esempio di risposta
        {
            "prodotti": [
                {id: 1, marca: "test", modello: "test", categoria: "test", prezzo: 10},
                {id: 2, marca: "test", modello: "test", categoria: "test", prezzo: 10},
                {id: 3, marca: "test", modello: "test", categoria: "test", prezzo: 10},
                {id: 4, marca: "test", modello: "test", categoria: "test", prezzo: 10},
            ]
        }
         */
        ArrayList<Prodotto> prodotti = prodottoDAO.getProdotti();
        System.out.println(prodotti);
        JSONObject jsonObject = new JSONObject();
        JSONArray array = new JSONArray();

        for(Prodotto p: prodotti){
            JSONObject provv = new JSONObject();
            provv.put("id", p.getId());
            provv.put("marca", p.getMarca());
            provv.put("modello", p.getModello());
            provv.put("categoria", p.getCategoria().getNomeCategoria());
            provv.put("prezzo", p.getPrezzo());

            array.put(provv);
        }

        jsonObject.put("prodotti",array);

        System.out.println(jsonObject.toString());

        return jsonObject.toString();
    }

    /*@
      @ public normal_behavior
      @   requires id > 0;
      @   signals (IOException e) true;
      @   signals (SQLException e) true;
      @*/
    public void eliminaProdotto(int id) throws IOException, SQLException {
        prodottoDAO.eliminaProdotto(id);
    }

    /*@
      @ public normal_behavior
      @   ensures \result != null;
      @   signals (IOException e) true;
      @   signals (SQLException e) true;
      @*/
    public String mostraCategorie() throws IOException, SQLException {
        ArrayList<Categoria> categorie = categoriaDAO.getCategorie();

        JSONObject jsonObject = new JSONObject();
        JSONArray array = new JSONArray();

        for(Categoria c: categorie){
            array.put(c.getNomeCategoria());
        }

        jsonObject.put("categorie",array);
        String risultato = jsonObject.toString();
        return risultato;
    }

    /*@
      @ public invariant utenteDAO != null;
      @ public invariant categoriaDAO != null;
      @ public invariant prodottoDAO != null;
      @ public invariant ordineDAO != null;
      @*/

    /*@
      @ public normal_behavior
      @   requires nome != null && nome.length() > 0;
      @   ensures \result == null; // Void method
      @   signals (IOException e) true;
      @   signals (SQLException e) true;
      @*/
    public void aggiungiCategoria(String nome) throws IOException, SQLException {
        Categoria c = new Categoria();
        c.setNomeCategoria(nome);
        categoriaDAO.addCategoria(c);
    }

    /*@
      @ public normal_behavior
      @   requires nome != null && nome.length() > 0;
      @   signals (IOException e) true;
      @   signals (SQLException e) true;
      @*/
    public void eliminaCategoria(String nome) throws IOException, SQLException {
        categoriaDAO.eliminaCategoria(nome);
    }

    /*@
      @ public normal_behavior
      @   ensures \result != null;
      @   signals (IOException e) true;
      @   signals (SQLException e) true;
      @*/
    public String mostraUtenti() throws IOException, SQLException {
        ArrayList<Utente> utenti = utenteDAO.getUtenti();

        JSONObject jsonObject = new JSONObject();
        JSONArray array = new JSONArray();

        for(Utente u: utenti){
            JSONObject provv = new JSONObject();
            provv.put("id", u.getId());
            provv.put("nome", u.getNome());
            provv.put("cognome", u.getCognome());
            provv.put("email", u.getEmail());
            provv.put("telefono", u.getTelefono());

            array.put(provv);
        }

        jsonObject.put("utenti",array);
        String risultato = jsonObject.toString();
        return risultato;
    }

    /*@
      @ public normal_behavior
      @   ensures \result != null;
      @   signals (IOException e) true;
      @   signals (SQLException e) true;
      @*/
    public String mostraOrdini()  throws IOException, SQLException {
        ArrayList<Ordine> ordini = ordineDAO.getOrdini();

        JSONObject jsonObject = new JSONObject();
        JSONArray array = new JSONArray();

        for(Ordine u: ordini){
            JSONObject provv = new JSONObject();
            provv.put("id", u.getId());
            provv.put("utente", u.getUtente().getId());
            provv.put("data", u.getDataOrdine() );
            provv.put("indirizzo", u.getIndirizzo());
            provv.put("totale", u.getPrezzoTotale());

            array.put(provv);
        }

        jsonObject.put("ordini",array);

        String risultato = jsonObject.toString();
        return risultato;
    }

    /*@
      @ public normal_behavior
      @   requires id != null;
      @   ensures \result != null;
      @   signals (IOException e) true;
      @   signals (SQLException e) true;
      @*/
    public String infoOrdine(Integer id) throws IOException, SQLException {
        Ordine o = ordineDAO.getOrdineById(id);
        Carrello c = ordineDAO.getProdottoOrdine(o);
        ArrayList<ProdottoCarrello> prodottiCarr = c.getProdotti();
        ArrayList<Prodotto> prodotti = new ArrayList<>();

        for(ProdottoCarrello p: prodottiCarr){
            prodotti.add(p.getProdotto());
        }

        JSONObject jsonObject = new JSONObject();
        JSONArray array = new JSONArray();
        int i = 0;
        for(Prodotto u: prodotti){
            JSONObject provv = new JSONObject();
            provv.put("id", u.getId());
            provv.put("marca", u.getMarca());
            provv.put("modello", u.getModello());
            provv.put("prezzo", u.getPrezzo());
            provv.put("quantita", prodottiCarr.get(i).getQuantita());
            array.put(provv);
            i++;
        }

        jsonObject.put("prodotti",array);
        jsonObject.put("totale", c.getTotaleCarrello());
        String risultato = jsonObject.toString();
        return risultato;
    }

    /*@
      @ public normal_behavior
      @   requires id != null;
      @   ensures \result != null;
      @   signals (IOException e) true;
      @   signals (SQLException e) true;
      @*/
    public String getProdotto(Integer id) throws IOException, SQLException {
        Prodotto p = prodottoDAO.getProdottoById(id);

        ArrayList<Specifiche> specifiche = p.getSpecifiche();
        JSONObject jsonObject= new JSONObject();
        JSONArray jsonArray = new JSONArray();

        jsonObject.put("marca", p.getMarca());
        jsonObject.put("modello", p.getModello());
        jsonObject.put("prezzo", p.getPrezzo());
        jsonObject.put("peso", p.getPeso());
        jsonObject.put("dimensioni", p.getDimensioni());
        jsonObject.put("categoria", p.getCategoria().getNomeCategoria());
        jsonObject.put("descrizione", p.getDescrizione());

        for(Specifiche s: specifiche){
            JSONObject provv = new JSONObject();
            provv.put("nome", s.getNome());
            provv.put("valore", s.getValore());
            jsonArray.put(provv);
        }

        jsonObject.put("specifiche", jsonArray);

        String risultato = jsonObject.toString();
        return risultato;
    }

    /*@
      @ public normal_behavior
      @   requires p != null;
      @   requires categoria != null;
      @   requires specifiche != null;
      @   signals (IOException e) true;
      @   signals (SQLException e) true;
      @*/
    public void modificaProdotto(Prodotto p, Categoria categoria, Part immagine, String specifiche)
            throws IOException, SQLException {

        p.setCategoria(categoria);

        // Se è stata passata una nuova immagine
        if (immagine != null && immagine.getSize() > 0) {
            String fileName = Paths.get(immagine.getSubmittedFileName()).getFileName().toString();
            p.setImmagine(fileName);

            try (InputStream fileStream = immagine.getInputStream()) {
                String currentDirectory = System.getProperty("user.dir");
                Path uploadPath = Paths.get(currentDirectory).getParent().resolve("upload");
                Files.createDirectories(uploadPath);

                File file = new File(uploadPath + File.separator + fileName);
                if (!file.exists()) {
                    Files.copy(fileStream, file.toPath());
                }
            }
        } else {
            p.setImmagine(null); // Mantieni null → il DAO deve interpretarlo come "non modificare immagine"
        }

        // Aggiorno i dati base del prodotto
        prodottoDAO.modificaProdotto(p);

        // Aggiorno le specifiche
        prodottoDAO.eliminaSpecificheProdotto(p.getId());

        JSONObject obj = new JSONObject(specifiche);
        JSONArray array = obj.getJSONArray("specifiche");
        ArrayList<Specifiche> list = new ArrayList<>();

        for (int i = 0; i < array.length(); i++) {
            Specifiche s = new Specifiche();
            s.setNome(array.getJSONObject(i).getString("nome"));
            s.setValore(array.getJSONObject(i).getString("valore"));
            list.add(s);
        }

        prodottoDAO.aggiungiSpecifiche(list, p.getId());
    }
}
