package controller;

import model.beans.Utente;
import services.RecensioniService;

import javax.servlet.RequestDispatcher;
import javax.servlet.ServletException;
import javax.servlet.annotation.WebServlet;
import javax.servlet.http.HttpServlet;
import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;
import java.io.IOException;
import java.sql.SQLException;

@WebServlet(name = "RecensioniServlet", urlPatterns = "/RecensioniServlet/*")
public class RecensioniServlet extends HttpServlet {
    private RecensioniService recensioniService;

    @Override
    public void init() throws ServletException {
        this.recensioniService = new RecensioniService();
    }

    @Override
    protected void doGet(HttpServletRequest request, HttpServletResponse response)
            throws ServletException, IOException {
        String path = request.getPathInfo() == null ? "/" : request.getPathInfo();

        if (path.equals("/aggiungiRecensione")) {
            try {
                Utente u = (Utente) request.getSession().getAttribute("user");
                if (u == null) {
                    response.sendError(HttpServletResponse.SC_UNAUTHORIZED);
                    return;
                    // String address = "/login.jsp";
                    // RequestDispatcher dispatcher = request.getRequestDispatcher(address);
                    // dispatcher.forward(request, response);
                    // return;
                }

                String testo = request.getParameter("testo");
                int valutazione = Integer.parseInt(request.getParameter("valutazione"));
                int idProdotto = Integer.parseInt(request.getParameter("idProdotto"));

                u = recensioniService.aggiungiRecensione(u, testo, valutazione, idProdotto);
                request.getSession().setAttribute("user", u);

            } catch (SQLException throwables) {
                throwables.printStackTrace();
                response.sendError(HttpServletResponse.SC_INTERNAL_SERVER_ERROR);
            }
        } else if (path.equals("/eliminaRecensione")) {
            try {
                Utente provv = (Utente) request.getSession().getAttribute("user");
                int idRecensione = Integer.parseInt(request.getParameter("recensione"));

                Utente u = recensioniService.eliminaRecensione(idRecensione, provv.getId());
                request.getSession().setAttribute("user", u);
                response.sendRedirect(request.getServletContext().getContextPath() + "/paginaUtente.jsp");
            } catch (SQLException throwables) {
                throwables.printStackTrace();
                response.sendError(HttpServletResponse.SC_INTERNAL_SERVER_ERROR);
            }
        } else {
            response.sendError(HttpServletResponse.SC_NOT_FOUND);
        }
    }

    @Override
    protected void doPost(HttpServletRequest request, HttpServletResponse response)
            throws ServletException, IOException {
        doGet(request, response);
    }
}
