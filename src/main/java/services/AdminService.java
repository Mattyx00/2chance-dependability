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
    public void aggiungiProdotto(Prodotto p, Categoria categoria, Part immagine, String specifiche) throws IOException, SQLException {
        ProdottoDAO dao = new ProdottoDAO();
        p.setCategoria(categoria);
        String fileName = Paths.get(immagine.getSubmittedFileName()).getFileName().toString();
        p.setImmagine(fileName);
        dao.addProdotto(p);

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

        dao.aggiungiSpecifiche(list, dao.getLastProduct());
    }

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
        System.out.println("sono arrivato qui CAZAZ");
        ProdottoDAO dao = new ProdottoDAO();
        ArrayList<Prodotto> prodotti = dao.getProdotti();
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

    public void eliminaProdotto(int id) throws IOException, SQLException {
        ProdottoDAO dao = new ProdottoDAO();
        dao.eliminaProdotto(id);
    }

    public String mostraCategorie() throws IOException, SQLException {
        CategoriaDAO dao = new CategoriaDAO();
        ArrayList<Categoria> categorie = dao.getCategorie();

        JSONObject jsonObject = new JSONObject();
        JSONArray array = new JSONArray();

        for(Categoria c: categorie){
            array.put(c.getNomeCategoria());
        }

        jsonObject.put("categorie",array);
        String risultato = jsonObject.toString();
        return risultato;
    }

    public void aggiungiCategoria(String nome) throws IOException, SQLException {
        CategoriaDAO dao = new CategoriaDAO();
        Categoria c = new Categoria();
        c.setNomeCategoria(nome);
        dao.addCategoria(c);
    }

    public void eliminaCategoria(String nome) throws IOException, SQLException {
        CategoriaDAO dao = new CategoriaDAO();
        dao.eliminaCategoria(nome);
    }

    public String mostraUtenti() throws IOException, SQLException {
        UtenteDAO utenteDAO = new UtenteDAO();
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

    public String mostraOrdini()  throws IOException, SQLException {
        OrdineDAO dao = new OrdineDAO();
        ArrayList<Ordine> ordini = dao.getOrdini();

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

    public String infoOrdine(Integer id) throws IOException, SQLException {
        OrdineDAO dao = new OrdineDAO();
        Ordine o = dao.getOrdineById(id);
        Carrello c = dao.getProdottoOrdine(o);
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

    public String getProdotto(Integer id) throws IOException, SQLException {
        ProdottoDAO dao = new ProdottoDAO();
        Prodotto p = dao.getProdottoById(id);

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

    public void modificaProdotto(Prodotto p, Categoria categoria, Part immagine, String specifiche)
            throws IOException, SQLException {

        ProdottoDAO dao = new ProdottoDAO();
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
        dao.modificaProdotto(p);

        // Aggiorno le specifiche
        dao.eliminaSpecificheProdotto(p.getId());

        JSONObject obj = new JSONObject(specifiche);
        JSONArray array = obj.getJSONArray("specifiche");
        ArrayList<Specifiche> list = new ArrayList<>();

        for (int i = 0; i < array.length(); i++) {
            Specifiche s = new Specifiche();
            s.setNome(array.getJSONObject(i).getString("nome"));
            s.setValore(array.getJSONObject(i).getString("valore"));
            list.add(s);
        }

        dao.aggiungiSpecifiche(list, p.getId());
    }
}
