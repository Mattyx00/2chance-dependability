package controller;

import model.beans.Categoria;
import model.beans.Prodotto;
import model.beans.Utente;
import services.AdminService;

import javax.servlet.RequestDispatcher;
import javax.servlet.ServletException;
import javax.servlet.annotation.MultipartConfig;
import javax.servlet.annotation.WebServlet;
import javax.servlet.http.HttpServlet;
import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;
import javax.servlet.http.Part;
import java.io.IOException;
import java.io.PrintWriter;
import java.sql.SQLException;


@MultipartConfig
@WebServlet(name = "AdminServlet", urlPatterns = "/AdminServlet/*")
public class AdminServlet extends HttpServlet {
    private AdminService adminService;

    @Override
    public void init() throws ServletException {
        try {
            this.adminService = new AdminService();
        } catch (SQLException e) {
            throw new ServletException("Failed to initialize AdminService", e);
        }
    }

    @Override
    protected void doGet(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
        String path = request.getPathInfo() == null ? "/" : request.getPathInfo();

        Utente user = (Utente) request.getSession().getAttribute("user");

        if (user == null || !user.isAdmin()) {
            String address = "/WEB-INF/error-pages/unauthorized.jsp";
            RequestDispatcher dispatcher = request.getRequestDispatcher(address);
            dispatcher.forward(request, response);
            return;
        }

        //refactored
        else if (path.equals("/aggiungiProdotto")) {
            try {
                Prodotto p = new Prodotto();

                p.setMarca(request.getParameter("marca"));
                p.setModello(request.getParameter("modello"));
                p.setPrezzo(Double.parseDouble(request.getParameter("prezzo")));
                p.setDescrizione(request.getParameter("descrizione"));
                p.setDimensioni(request.getParameter("dimensioni"));
                p.setPeso(Double.parseDouble(request.getParameter("peso")));
                Categoria categoria = new Categoria();
                categoria.setNomeCategoria(request.getParameter("categoria"));
                Part immagine = request.getPart("immagine");
                String specifiche = request.getParameter("specifiche");
                adminService.aggiungiProdotto(p, categoria, immagine, specifiche);
                return;
            } catch (SQLException e) {
                e.printStackTrace();
                response.sendError(HttpServletResponse.SC_INTERNAL_SERVER_ERROR);
            }
        }
        //refactored
        else if (path.equals("/mostraProdotti")) {
            try {
                String risultato = adminService.mostraProdotti();
                //Invio il json di risposta che il contenuto (contentType) sia di tipo json
                PrintWriter out = response.getWriter();
                response.setContentType("application/json");
                response.setCharacterEncoding("UTF-8");
                out.print(risultato);
                out.flush();
            } catch (SQLException throwables) {
                throwables.printStackTrace();
                response.sendError(HttpServletResponse.SC_INTERNAL_SERVER_ERROR);
            } finally {
                return;
            }
        }

        //refactored
        else if (path.equals("/eliminaProdotto")) {
            try {
                adminService.eliminaProdotto(Integer.parseInt(request.getParameter("id")));
            } catch (SQLException throwables) {
                throwables.printStackTrace();
            } finally {
                return;
            }
        }

        //refactored
        else if (path.equals("/mostraCategorie")) {
            try {
                String risultato = adminService.mostraCategorie();

                PrintWriter out = response.getWriter();
                response.setContentType("application/json");
                response.setCharacterEncoding("UTF-8");
                out.print(risultato);
                out.flush();
            } catch (SQLException throwables) {
                throwables.printStackTrace();
            } finally {
                return;
            }
        }
        //refactored
        else if (path.equals("/aggiungiCategoria")) {
            try {
                adminService.aggiungiCategoria(request.getParameter("nomeCategoria"));
            } catch (SQLException throwables) {
                throwables.printStackTrace();
            } finally {
                return;
            }
        }
        //refactored
        else if (path.equals("/eliminaCategoria")) {
            try {
                adminService.eliminaCategoria(request.getParameter("nomeCategoria"));
            } catch (SQLException throwables) {
                throwables.printStackTrace();
            } finally {
                return;
            }
        }
        //refactored
        else if (path.equals("/mostraUtenti")) {
            try {
                String risultato = adminService.mostraUtenti();

                PrintWriter out = response.getWriter();
                response.setContentType("application/json");
                response.setCharacterEncoding("UTF-8");
                out.print(risultato);
                out.flush();
            } catch (SQLException throwables) {
                throwables.printStackTrace();
            } finally {
                return;
            }
        }

        //refactored
        else if (path.equals("/mostraOrdini")) {
            try {

                String risultato = adminService.mostraOrdini();

                PrintWriter out = response.getWriter();
                response.setContentType("application/json");
                response.setCharacterEncoding("UTF-8");
                out.print(risultato);
                out.flush();

            } catch (SQLException throwables) {
                throwables.printStackTrace();
            } finally {
                return;
            }
        }

        //refactored
        else if (path.equals("/infoOrdine")) {
            try {
                String risultato = adminService.infoOrdine(Integer.parseInt(request.getParameter("idOrdine")));

                PrintWriter out = response.getWriter();
                response.setContentType("application/json");
                response.setCharacterEncoding("UTF-8");
                out.print(risultato);
                out.flush();
            } catch (SQLException throwables) {
                throwables.printStackTrace();
            } finally {
                return;
            }
        }

        //refactored
        else if (path.equals("/getProdotto")) {
            try {
                int idProdotto = Integer.parseInt(request.getParameter("idProdotto"));
                String risultato = adminService.getProdotto(idProdotto);

                PrintWriter out = response.getWriter();
                response.setContentType("application/json");
                response.setCharacterEncoding("UTF-8");
                out.print(risultato);
                out.flush();
            } catch (SQLException throwables) {
                throwables.printStackTrace();
            } finally {
                return;
            }

        }
        //refactored
        else if (path.equals("/modificaProdotto")) {
            try {
                Prodotto p = new Prodotto();

                p.setMarca(request.getParameter("marca"));
                p.setModello(request.getParameter("modello"));
                p.setPrezzo(Double.parseDouble(request.getParameter("prezzo")));
                p.setDescrizione(request.getParameter("descrizione"));
                p.setDimensioni(request.getParameter("dimensioni"));
                p.setPeso(Double.parseDouble(request.getParameter("peso")));
                p.setId(Integer.parseInt(request.getParameter("id")));

                Categoria categoria = new Categoria();
                categoria.setNomeCategoria(request.getParameter("categoria"));

                Part immagine = request.getPart("immagine");
                String specifiche = request.getParameter("specifiche");

                adminService.modificaProdotto(p, categoria, immagine, specifiche);
                return;

            } catch (Exception e) {
                e.printStackTrace();
                response.sendError(HttpServletResponse.SC_INTERNAL_SERVER_ERROR);
            }
        }
    }

        @Override
    protected void doPost(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
        doGet(request, response);
    }
}
