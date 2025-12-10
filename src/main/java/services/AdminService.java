package services;

import model.beans.*;
import model.dao.CategoriaDAO;
import model.dao.OrdineDAO;
import model.dao.ProdottoDAO;
import model.dao.UtenteDAO;
import org.json.JSONArray;
import org.json.JSONException;
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
    private final ProdottoDAO prodottoDAO;
    private final CategoriaDAO categoriaDAO;
    private final UtenteDAO utenteDAO;
    private final OrdineDAO ordineDAO;

    /*
     * @
     * 
     * @ public normal_behavior
     * 
     * @ ensures prodottoDAO != null;
     * 
     * @ ensures categoriaDAO != null;
     * 
     * @ ensures utenteDAO != null;
     * 
     * @ ensures ordineDAO != null;
     * 
     * @ signals (SQLException e) true;
     * 
     * @
     */
    public AdminService() throws SQLException {
        this.prodottoDAO = new ProdottoDAO();
        this.categoriaDAO = new CategoriaDAO();
        this.utenteDAO = new UtenteDAO();
        this.ordineDAO = new OrdineDAO();
    }

    /*
     * @
     * 
     * @ public normal_behavior
     * 
     * @ requires prodottoDAO != null;
     * 
     * @ requires categoriaDAO != null;
     * 
     * @ requires utenteDAO != null;
     * 
     * @ requires ordineDAO != null;
     * 
     * @ ensures this.prodottoDAO == prodottoDAO;
     * 
     * @ ensures this.categoriaDAO == categoriaDAO;
     * 
     * @ ensures this.utenteDAO == utenteDAO;
     * 
     * @ ensures this.ordineDAO == ordineDAO;
     * 
     * @
     */
    public AdminService(ProdottoDAO prodottoDAO, CategoriaDAO categoriaDAO, UtenteDAO utenteDAO, OrdineDAO ordineDAO) {
        if (prodottoDAO == null)
            throw new IllegalArgumentException("ProdottoDAO cannot be null");
        if (categoriaDAO == null)
            throw new IllegalArgumentException("CategoriaDAO cannot be null");
        if (utenteDAO == null)
            throw new IllegalArgumentException("UtenteDAO cannot be null");
        if (ordineDAO == null)
            throw new IllegalArgumentException("OrdineDAO cannot be null");

        this.prodottoDAO = prodottoDAO;
        this.categoriaDAO = categoriaDAO;
        this.utenteDAO = utenteDAO;
        this.ordineDAO = ordineDAO;
    }

    /*
     * @
     * 
     * @ public normal_behavior
     * 
     * @ requires p != null;
     * 
     * @ requires categoria != null;
     * 
     * @ requires immagine != null;
     * 
     * @ requires specifiche != null;
     * 
     * @ signals (IOException e) true;
     * 
     * @ signals (SQLException e) true;
     * 
     * @
     */
    public void aggiungiProdotto(Prodotto p, Categoria categoria, Part immagine, String specifiche)
            throws IOException, SQLException {
        if (p == null)
            throw new IllegalArgumentException("Prodotto cannot be null");
        if (categoria == null)
            throw new IllegalArgumentException("Categoria cannot be null");
        if (immagine == null)
            throw new IllegalArgumentException("Immagine Part cannot be null");
        if (specifiche == null || specifiche.trim().isEmpty())
            throw new IllegalArgumentException("Specifiche string cannot be null or empty");

        p.setCategoria(categoria);
        String submittedFileName = immagine.getSubmittedFileName();
        if (submittedFileName == null)
            throw new IllegalArgumentException("Image file name cannot be null");

        String fileName = Paths.get(submittedFileName).getFileName().toString();
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
        try {
            JSONObject obj = new JSONObject(specifiche);
            JSONArray array = obj.getJSONArray("specifiche");
            ArrayList<Specifiche> list = new ArrayList<>();

            for (int i = 0; i < array.length(); i++) {
                Specifiche s = new Specifiche();
                s.setNome(array.getJSONObject(i).getString("nome"));
                s.setValore(array.getJSONObject(i).getString("valore"));
                list.add(s);
            }

            int lastProductId = prodottoDAO.getLastProduct();
            if (lastProductId <= 0)
                throw new IllegalStateException("Failed to retrieve the last added product ID.");

            prodottoDAO.aggiungiSpecifiche(list, lastProductId);
        } catch (JSONException e) {
            throw new IllegalArgumentException("Invalid JSON format for specifiche", e);
        }
    }

    /*
     * @
     * 
     * @ public normal_behavior
     * 
     * @ ensures \result != null;
     * 
     * @ signals (IOException e) true;
     * 
     * @ signals (SQLException e) true;
     * 
     * @
     */
    public String mostraProdotti() throws IOException, SQLException {
        ArrayList<Prodotto> prodotti = prodottoDAO.getProdotti();
        if (prodotti == null)
            throw new IllegalStateException("DAO returned null for prodotti list");

        JSONObject jsonObject = new JSONObject();
        JSONArray array = new JSONArray();

        for (Prodotto p : prodotti) {
            if (p == null)
                continue; // Skip null products if any
            JSONObject provv = new JSONObject();
            provv.put("id", p.getId());
            provv.put("marca", p.getMarca());
            provv.put("modello", p.getModello());
            if (p.getCategoria() != null) {
                provv.put("categoria", p.getCategoria().getNomeCategoria());
            } else {
                provv.put("categoria", "N/A");
            }
            provv.put("prezzo", p.getPrezzo());

            array.put(provv);
        }

        jsonObject.put("prodotti", array);

        return jsonObject.toString();
    }

    /*
     * @
     * 
     * @ public normal_behavior
     * 
     * @ requires id > 0;
     * 
     * @ signals (IOException e) true;
     * 
     * @ signals (SQLException e) true;
     * 
     * @
     */
    public void eliminaProdotto(int id) throws IOException, SQLException {
        if (id <= 0)
            throw new IllegalArgumentException("Product ID must be greater than 0");
        prodottoDAO.eliminaProdotto(id);
    }

    /*
     * @
     * 
     * @ public normal_behavior
     * 
     * @ ensures \result != null;
     * 
     * @ signals (IOException e) true;
     * 
     * @ signals (SQLException e) true;
     * 
     * @
     */
    public String mostraCategorie() throws IOException, SQLException {
        ArrayList<Categoria> categorie = categoriaDAO.getCategorie();
        if (categorie == null)
            throw new IllegalStateException("DAO returned null for categorie list");

        JSONObject jsonObject = new JSONObject();
        JSONArray array = new JSONArray();

        for (Categoria c : categorie) {
            if (c != null) {
                array.put(c.getNomeCategoria());
            }
        }

        jsonObject.put("categorie", array);
        return jsonObject.toString();
    }

    /*
     * @
     * 
     * @ public invariant utenteDAO != null;
     * 
     * @ public invariant categoriaDAO != null;
     * 
     * @ public invariant prodottoDAO != null;
     * 
     * @ public invariant ordineDAO != null;
     * 
     * @
     */

    /*
     * @
     * 
     * @ public normal_behavior
     * 
     * @ requires nome != null && nome.length() > 0;
     * 
     * @ ensures \result == null; // Void method
     * 
     * @ signals (IOException e) true;
     * 
     * @ signals (SQLException e) true;
     * 
     * @
     */
    public void aggiungiCategoria(String nome) throws IOException, SQLException {
        if (nome == null || nome.trim().isEmpty()) {
            throw new IllegalArgumentException("Categoria name cannot be null or empty");
        }
        Categoria c = new Categoria();
        c.setNomeCategoria(nome);
        categoriaDAO.addCategoria(c);
    }

    /*
     * @
     * 
     * @ public normal_behavior
     * 
     * @ requires nome != null && nome.length() > 0;
     * 
     * @ signals (IOException e) true;
     * 
     * @ signals (SQLException e) true;
     * 
     * @
     */
    public void eliminaCategoria(String nome) throws IOException, SQLException {
        if (nome == null || nome.trim().isEmpty()) {
            throw new IllegalArgumentException("Categoria name cannot be null or empty");
        }
        categoriaDAO.eliminaCategoria(nome);
    }

    /*
     * @
     * 
     * @ public normal_behavior
     * 
     * @ ensures \result != null;
     * 
     * @ signals (IOException e) true;
     * 
     * @ signals (SQLException e) true;
     * 
     * @
     */
    public String mostraUtenti() throws IOException, SQLException {
        ArrayList<Utente> utenti = utenteDAO.getUtenti();
        if (utenti == null)
            throw new IllegalStateException("DAO returned null for utenti list");

        JSONObject jsonObject = new JSONObject();
        JSONArray array = new JSONArray();

        for (Utente u : utenti) {
            if (u == null)
                continue;
            JSONObject provv = new JSONObject();
            provv.put("id", u.getId());
            provv.put("nome", u.getNome());
            provv.put("cognome", u.getCognome());
            provv.put("email", u.getEmail());
            provv.put("telefono", u.getTelefono());

            array.put(provv);
        }

        jsonObject.put("utenti", array);
        return jsonObject.toString();
    }

    /*
     * @
     * 
     * @ public normal_behavior
     * 
     * @ ensures \result != null;
     * 
     * @ signals (IOException e) true;
     * 
     * @ signals (SQLException e) true;
     * 
     * @
     */
    public String mostraOrdini() throws IOException, SQLException {
        ArrayList<Ordine> ordini = ordineDAO.getOrdini();
        if (ordini == null)
            throw new IllegalStateException("DAO returned null for ordini list");

        JSONObject jsonObject = new JSONObject();
        JSONArray array = new JSONArray();

        for (Ordine u : ordini) {
            if (u == null)
                continue;
            JSONObject provv = new JSONObject();
            provv.put("id", u.getId());
            if (u.getUtente() != null) {
                provv.put("utente", u.getUtente().getId());
            } else {
                provv.put("utente", "Unknown");
            }
            provv.put("data", u.getDataOrdine());
            provv.put("indirizzo", u.getIndirizzo());
            provv.put("totale", u.getPrezzoTotale());

            array.put(provv);
        }

        jsonObject.put("ordini", array);
        return jsonObject.toString();
    }

    /*
     * @
     * 
     * @ public normal_behavior
     * 
     * @ requires id != null;
     * 
     * @ ensures \result != null;
     * 
     * @ signals (IOException e) true;
     * 
     * @ signals (SQLException e) true;
     * 
     * @
     */
    public String infoOrdine(Integer id) throws IOException, SQLException {
        if (id == null || id <= 0)
            throw new IllegalArgumentException("Order ID must be non-null and positive");

        Ordine o = ordineDAO.getOrdineById(id);
        if (o == null)
            throw new IllegalArgumentException("Order not found with ID: " + id);

        Carrello c = ordineDAO.getProdottoOrdine(o);
        if (c == null)
            throw new IllegalStateException("Cart associated with order is null");

        ArrayList<ProdottoCarrello> prodottiCarr = c.getProdotti();
        if (prodottiCarr == null)
            prodottiCarr = new ArrayList<>(); // Defensive empty list

        JSONObject jsonObject = new JSONObject();
        JSONArray array = new JSONArray();

        // Revised robust loop:
        for (ProdottoCarrello pc : prodottiCarr) {
            if (pc == null || pc.getProdotto() == null)
                continue;
            Prodotto p = pc.getProdotto();

            JSONObject provv = new JSONObject();
            provv.put("id", p.getId());
            provv.put("marca", p.getMarca());
            provv.put("modello", p.getModello());
            provv.put("prezzo", p.getPrezzo());
            provv.put("quantita", pc.getQuantita());
            array.put(provv);
        }

        jsonObject.put("prodotti", array);
        jsonObject.put("totale", c.getTotaleCarrello());
        return jsonObject.toString();
    }

    /*
     * @
     * 
     * @ public normal_behavior
     * 
     * @ requires id != null;
     * 
     * @ ensures \result != null;
     * 
     * @ signals (IOException e) true;
     * 
     * @ signals (SQLException e) true;
     * 
     * @
     */
    public String getProdotto(Integer id) throws IOException, SQLException {
        if (id == null || id <= 0)
            throw new IllegalArgumentException("Product ID must be non-null and positive");

        Prodotto p = prodottoDAO.getProdottoById(id);
        if (p == null)
            throw new IllegalArgumentException("Product not found with ID: " + id);

        ArrayList<Specifiche> specifiche = p.getSpecifiche();
        JSONObject jsonObject = new JSONObject();
        JSONArray jsonArray = new JSONArray();

        jsonObject.put("marca", p.getMarca());
        jsonObject.put("modello", p.getModello());
        jsonObject.put("prezzo", p.getPrezzo());
        jsonObject.put("peso", p.getPeso());
        jsonObject.put("dimensioni", p.getDimensioni());
        if (p.getCategoria() != null) {
            jsonObject.put("categoria", p.getCategoria().getNomeCategoria());
        } else {
            jsonObject.put("categoria", "N/A");
        }
        jsonObject.put("descrizione", p.getDescrizione());

        if (specifiche != null) {
            for (Specifiche s : specifiche) {
                if (s == null)
                    continue;
                JSONObject provv = new JSONObject();
                provv.put("nome", s.getNome());
                provv.put("valore", s.getValore());
                jsonArray.put(provv);
            }
        }

        jsonObject.put("specifiche", jsonArray);

        return jsonObject.toString();
    }

    /*
     * @
     * 
     * @ public normal_behavior
     * 
     * @ requires p != null;
     * 
     * @ requires categoria != null;
     * 
     * @ requires specifiche != null;
     * 
     * @ signals (IOException e) true;
     * 
     * @ signals (SQLException e) true;
     * 
     * @
     */
    public void modificaProdotto(Prodotto p, Categoria categoria, Part immagine, String specifiche)
            throws IOException, SQLException {

        if (p == null)
            throw new IllegalArgumentException("Prodotto cannot be null");
        if (categoria == null)
            throw new IllegalArgumentException("Categoria cannot be null");
        if (specifiche == null)
            throw new IllegalArgumentException("Specifiche string cannot be null");

        p.setCategoria(categoria);

        // Se è stata passata una nuova immagine
        if (immagine != null && immagine.getSize() > 0) {
            String submittedFileName = immagine.getSubmittedFileName();
            if (submittedFileName != null) {
                String fileName = Paths.get(submittedFileName).getFileName().toString();
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
            }
        } else {
            p.setImmagine(null); // Mantieni null → il DAO deve interpretarlo come "non modificare immagine"
        }

        // Aggiorno i dati base del prodotto
        prodottoDAO.modificaProdotto(p);

        // Aggiorno le specifiche
        prodottoDAO.eliminaSpecificheProdotto(p.getId());

        try {
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
        } catch (JSONException e) {
            throw new IllegalArgumentException("Invalid JSON format for specifiche", e);
        }
    }
}
