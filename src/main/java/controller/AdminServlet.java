package controller;

import model.beans.*;
import model.dao.CategoriaDAO;
import model.dao.OrdineDAO;
import model.dao.ProdottoDAO;
import model.dao.UtenteDAO;
import org.json.JSONArray;
import org.json.JSONObject;

import javax.servlet.*;
import javax.servlet.http.*;
import javax.servlet.annotation.*;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.PrintWriter;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.sql.SQLException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

@MultipartConfig
@WebServlet(name = "AdminServlet", urlPatterns = "/AdminServlet/*")
public class AdminServlet extends HttpServlet {
    @Override
    protected void doGet(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
        String path = request.getPathInfo() == null ? "/" : request.getPathInfo();

        Utente user = (Utente) request.getSession().getAttribute("user");

        if(user == null || !user.isAdmin()){
            String address = "/WEB-INF/error-pages/unauthorized.jsp";
            RequestDispatcher dispatcher = request.getRequestDispatcher(address);
            dispatcher.forward(request, response);
            return;
        }

        if(path.equals("/aggiungiProdotto")){
            try {
                ProdottoDAO dao = new ProdottoDAO();
                Prodotto p = new Prodotto();
                p.setMarca(request.getParameter("marca"));
                p.setModello(request.getParameter("modello"));
                p.setPrezzo(Double.parseDouble(request.getParameter("prezzo")));
                p.setDescrizione(request.getParameter("descrizione"));
                p.setDimensioni(request.getParameter("dimensioni"));
                p.setPeso(Double.parseDouble(request.getParameter("peso")));

                Categoria provv = new Categoria();
                provv.setNomeCategoria(request.getParameter("categoria"));
                p.setCategoria(provv);

                Part part = request.getPart("immagine");
                String fileName = Paths.get(part.getSubmittedFileName()).getFileName().toString(); //nome immagine

                p.setImmagine(fileName);
                dao.addProdotto(p);

                File file;
                try (InputStream fileStream = part.getInputStream()) { //ottengo il path corrente e salvo l'immagine in upload
                    String currentDirectory = System.getProperty("user.dir");
                    Path currentPath = Paths.get(currentDirectory);
                    Path parentPath = currentPath.getParent(); // Ottiene il percorso del genitore
                    Path uploadPath = parentPath.resolve("upload"); // Risolve "upload" nel percorso del genitore

                    String uploadRoot = uploadPath.toString() + File.separator;

                    file = new File(uploadRoot + fileName);
                    if (!file.exists())
                        Files.copy(fileStream, file.toPath());
                }


            } catch (SQLException throwables) {
                throwables.printStackTrace();
            }
            JSONObject obj = new JSONObject(request.getParameter("specifiche"));

            ArrayList<Specifiche> list = new ArrayList<>();
            JSONArray array = obj.getJSONArray("specifiche");
            for(int i = 0 ; i < array.length() ; i++){
                Specifiche s = new Specifiche();
                s.setNome(array.getJSONObject(i).getString("nome"));
                s.setValore(array.getJSONObject(i).getString("valore"));
                list.add(s);
            }

            try {
                ProdottoDAO  dao = new ProdottoDAO();
                dao.aggiungiSpecifiche(list, dao.getLastProduct());
            } catch (SQLException throwables) {
                throwables.printStackTrace();
            }finally {
                return;
            }
        }

        if(path.equals("/mostraProdotti")){
            ProdottoDAO dao = null;
            try {
                dao = new ProdottoDAO();
                ArrayList<Prodotto> prodotti2 = dao.getProdotti();

                 /*Esempio di json
                {
                    "prodotti": [
                        {id: 1, marca: "test", modello: "test", categoria: "test", prezzo: 10},
                        {id: 2, marca: "test", modello: "test", categoria: "test", prezzo: 10},
                        {id: 3, marca: "test", modello: "test", categoria: "test", prezzo: 10},
                        {id: 4, marca: "test", modello: "test", categoria: "test", prezzo: 10},
                    ]
                }
                 */

                JSONObject jsonObject = new JSONObject();
                JSONArray array = new JSONArray();

                for(Prodotto p: prodotti2){
                    JSONObject provv = new JSONObject();
                    provv.put("id", p.getId());
                    provv.put("marca", p.getMarca());
                    provv.put("modello", p.getModello());
                    provv.put("categoria", p.getCategoria().getNomeCategoria());
                    provv.put("prezzo", p.getPrezzo());

                    array.put(provv);
                }

                jsonObject.put("prodotti",array);
                String risultato = jsonObject.toString();

                //Invio il json di risposta che il contenuto (contentType) sia di tipo json
                PrintWriter out = response.getWriter();
                response.setContentType("application/json");
                response.setCharacterEncoding("UTF-8");
                out.print(risultato);
                out.flush();
            } catch (SQLException throwables) {
                throwables.printStackTrace();
            }finally {
                return;
            }
        }

        if(path.equals("/eliminaProdotto")){
            try {
                ProdottoDAO dao = new ProdottoDAO();
                dao.eliminaProdotto(Integer.parseInt(request.getParameter("id")));
            } catch (SQLException throwables) {
                throwables.printStackTrace();
            }finally {
                return;
            }
        }

        if(path.equals("/mostraCategorie")){

            try {
                CategoriaDAO dao = new CategoriaDAO();
                ArrayList<Categoria> categorie = dao.getCategorie();

                JSONObject jsonObject = new JSONObject();
                JSONArray array = new JSONArray();

                for(Categoria c: categorie){
                    array.put(c.getNomeCategoria());
                }

                jsonObject.put("categorie",array);
                String risultato = jsonObject.toString();

                PrintWriter out = response.getWriter();
                response.setContentType("application/json");
                response.setCharacterEncoding("UTF-8");
                out.print(risultato);
                out.flush();
            } catch (SQLException throwables) {
                throwables.printStackTrace();
            }finally {
                return;
            }
        }

        else if(path.equals("/aggiungiCategoria")){
            try {
                CategoriaDAO dao = new CategoriaDAO();
                Categoria c = new Categoria();
                c.setNomeCategoria(request.getParameter("nomeCategoria"));
                dao.addCategoria(c);
            } catch (SQLException throwables) {
                throwables.printStackTrace();
            }finally {
                return;
            }
        }

        else if(path.equals("/eliminaCategoria")){
            try {
                CategoriaDAO dao = new CategoriaDAO();
                dao.eliminaCategoria(request.getParameter("nomeCategoria"));

            } catch (SQLException throwables) {
                throwables.printStackTrace();
            }finally {
                return;
            }
        }

        else if(path.equals("/mostraUtenti")){
            try {
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

                PrintWriter out = response.getWriter();
                response.setContentType("application/json");
                response.setCharacterEncoding("UTF-8");
                out.print(risultato);
                out.flush();
        } catch (SQLException throwables) {
                throwables.printStackTrace();
            }finally {
                return;
            }
        }

        else if(path.equals("/mostraOrdini")){
            try {
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

                PrintWriter out = response.getWriter();
                response.setContentType("application/json");
                response.setCharacterEncoding("UTF-8");
                out.print(risultato);
                out.flush();

            } catch (SQLException throwables) {
                throwables.printStackTrace();
            }finally {
                return;
            }
        }

        else if(path.equals("/infoOrdine")){
            OrdineDAO dao = null;
            try {
                dao = new OrdineDAO();
                Ordine o = dao.getOrdineById(Integer.parseInt(request.getParameter("idOrdine")));
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

                PrintWriter out = response.getWriter();
                response.setContentType("application/json");
                response.setCharacterEncoding("UTF-8");
                out.print(risultato);
                out.flush();
            } catch (SQLException throwables) {
                throwables.printStackTrace();
            }finally {
                return;
            }
        }

        else if(path.equals("/getProdotto")){
            int idProdotto = Integer.parseInt(request.getParameter("idProdotto"));
            ProdottoDAO dao = null;
            try {
                dao = new ProdottoDAO();
                Prodotto p = dao.getProdottoById(idProdotto);

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

                PrintWriter out = response.getWriter();
                response.setContentType("application/json");
                response.setCharacterEncoding("UTF-8");
                out.print(risultato);
                out.flush();
            } catch (SQLException throwables) {
                throwables.printStackTrace();
            }finally {
                return;
            }

        }

       else if(path.equals("/modificaProdotto")){
            try {
                ProdottoDAO dao = new ProdottoDAO();
                Prodotto p = new Prodotto();
                p.setMarca(request.getParameter("marca"));
                p.setModello(request.getParameter("modello"));
                p.setPrezzo(Double.parseDouble(request.getParameter("prezzo")));
                p.setDescrizione(request.getParameter("descrizione"));
                p.setDimensioni(request.getParameter("dimensioni"));
                p.setPeso(Double.parseDouble(request.getParameter("peso")));
                p.setId(Integer.parseInt(request.getParameter("id")));


                Categoria provv = new Categoria();
                provv.setNomeCategoria(request.getParameter("categoria"));
                p.setCategoria(provv);

                if(request.getPart("immagine") != null) {
                    Part part = request.getPart("immagine");
                    String fileName = Paths.get(part.getSubmittedFileName()).getFileName().toString(); //nome immagine
                    p.setImmagine(fileName);

                    File file;
                    try (InputStream fileStream = part.getInputStream()) {

                        String currentDirectory = System.getProperty("user.dir"); //ottengo il path corrente e salvo l'immagine in upload
                        Path currentPath = Paths.get(currentDirectory);
                        Path parentPath = currentPath.getParent(); // Ottiene il percorso del genitore
                        Path uploadPath = parentPath.resolve("upload"); // Risolve "upload" nel percorso del genitore

                        String uploadRoot = uploadPath.toString() + File.separator;
                        file = new File(uploadRoot + fileName);
                        if (!file.exists())
                            Files.copy(fileStream, file.toPath());
                    }
                }else{
                    p.setImmagine(null);
                }

                dao.modificaProdotto(p);

            } catch (SQLException throwables) {
                throwables.printStackTrace();
            }

            try {
                ProdottoDAO dao = new ProdottoDAO();
                dao.eliminaSpecificheProdotto(Integer.parseInt(request.getParameter("id")));
            } catch (SQLException throwables) {
                throwables.printStackTrace();
            }

            JSONObject obj = new JSONObject(request.getParameter("specifiche"));

            ArrayList<Specifiche> list = new ArrayList<>();
            JSONArray array = obj.getJSONArray("specifiche");
            for(int i = 0 ; i < array.length() ; i++){
                Specifiche s = new Specifiche();
                s.setNome(array.getJSONObject(i).getString("nome"));
                s.setValore(array.getJSONObject(i).getString("valore"));
                list.add(s);

            }

            try {
                ProdottoDAO  dao = new ProdottoDAO();
                dao.aggiungiSpecifiche(list, Integer.parseInt(request.getParameter("id")));
            } catch (SQLException throwables) {
                throwables.printStackTrace();
            }finally {
                return;
            }
        }

        else{
            response.sendError(HttpServletResponse.SC_NOT_FOUND);
        }
    }

    @Override
    protected void doPost(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
        doGet(request, response);
    }
}
