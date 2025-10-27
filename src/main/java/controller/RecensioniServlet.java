package controller;

import model.beans.Prodotto;
import model.beans.Recensione;
import model.beans.Utente;
import model.dao.ProdottoDAO;
import model.dao.RecensioneDAO;
import model.dao.UtenteDAO;

import javax.servlet.*;
import javax.servlet.http.*;
import javax.servlet.annotation.*;
import java.io.IOException;
import java.sql.SQLException;
import java.util.ArrayList;

@WebServlet(name = "RecensioniServlet", urlPatterns = "/RecensioniServlet/*")
public class RecensioniServlet extends HttpServlet {
    @Override
    protected void doGet(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
        String path = request.getPathInfo() == null ? "/" : request.getPathInfo();

        if(path.equals("/aggiungiRecensione")){
            try {
                if(request.getSession().getAttribute("user") == null){
                    String address = "/login.jsp";
                    RequestDispatcher dispatcher = request.getRequestDispatcher(address);
                    dispatcher.forward(request, response);
                }

                RecensioneDAO dao = new RecensioneDAO();
                Recensione r = new Recensione();
                r.setTesto(request.getParameter("testo"));
                r.setValutazione(Integer.parseInt(request.getParameter("valutazione")));
                r.setUtente((Utente)request.getSession().getAttribute("user"));
                ProdottoDAO pDao = new ProdottoDAO();
                r.setProdotto(pDao.getProdottoById(Integer.parseInt(request.getParameter("idProdotto"))));
                dao.addRecensione(r);
                Utente u = (Utente)request.getSession().getAttribute("user");
                ArrayList<Recensione> recensioni = dao.getRecensioniByUtente(u);
                u.setRecensioni(recensioni);
                request.getSession().setAttribute("user", u);
            } catch (SQLException throwables) {
                throwables.printStackTrace();
            }
        }

        else if(path.equals("/eliminaRecensione")){
            try {
                RecensioneDAO dao = new RecensioneDAO();
                dao.deleteRecensione(Integer.parseInt(request.getParameter("recensione")));
                UtenteDAO uDao  = new UtenteDAO();
                Utente provv = (Utente)request.getSession().getAttribute("user");
                Utente u = uDao.getUtenteById(provv.getId());
                request.getSession().setAttribute("user", u);
                response.sendRedirect( request.getServletContext().getContextPath()+"/paginaUtente.jsp");
            } catch (SQLException throwables) {
                throwables.printStackTrace();
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
