package controller;

import model.beans.Carrello;
import model.beans.Utente;
import services.CheckOutService;

import java.sql.SQLException;

import javax.servlet.ServletException;

import javax.servlet.annotation.WebServlet;
import javax.servlet.http.HttpServlet;
import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;
import javax.servlet.http.HttpSession;
import java.io.IOException;

@WebServlet(name = "CheckOutServlet", value = "/CheckOutServlet")
public class CheckOutServlet extends HttpServlet {

    private CheckOutService checkOutService;

    @Override
    public void init() throws ServletException {
        try {
            this.checkOutService = new CheckOutService();
        } catch (SQLException e) {
            throw new ServletException("Failed to initialize CheckOutService", e);
        }
    }

    @Override
    protected void doGet(HttpServletRequest request, HttpServletResponse response)
            throws ServletException, IOException {
        try {
            HttpSession session = request.getSession();

            // Devi essere loggato
            Utente utente = (Utente) session.getAttribute("user");
            if (utente == null) {
                response.sendRedirect(request.getContextPath() + "/login.jsp");
                return;
            }

            Carrello carrello = (Carrello) session.getAttribute("carrello");
            if (carrello == null || carrello.getProdotti().isEmpty()) {
                response.sendRedirect(request.getContextPath() + "/carrello.jsp");
                return;
            }

            String indirizzo = request.getParameter("indirizzo");

            try {
                // Checkout effettivo
                checkOutService.effettuaCheckout(utente, carrello, indirizzo);

                // Aggiorna ordini dell’utente in sessione
                Utente utenteAggiornato = checkOutService.aggiornaOrdiniUtente(utente);
                session.setAttribute("user", utenteAggiornato);

                // Svuota il carrello
                session.removeAttribute("carrello");

                response.sendRedirect(request.getContextPath() + "/landingpage");

            } catch (Exception e) {
                e.printStackTrace();
                response.sendError(HttpServletResponse.SC_INTERNAL_SERVER_ERROR);
            }
        } catch (Exception e) {
            e.printStackTrace();
        }
    }

    @Override
    protected void doPost(HttpServletRequest request, HttpServletResponse response)
            throws ServletException, IOException {
        try {
            doGet(request, response);
        } catch (Exception e) {
            e.printStackTrace();
        }
    }
}
