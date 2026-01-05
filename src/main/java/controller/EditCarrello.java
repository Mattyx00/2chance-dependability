package controller;

import model.beans.Carrello;
import services.EditCarrelloService;

import java.sql.SQLException;

import javax.servlet.ServletException;
import javax.servlet.annotation.WebServlet;
import javax.servlet.http.HttpServlet;
import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;
import javax.servlet.http.HttpSession;
import java.io.IOException;

@WebServlet(name = "EditCarrello", value = "/EditCarrello")
public class EditCarrello extends HttpServlet {

    private EditCarrelloService editCarrelloService;

    @Override
    public void init() throws ServletException {
        try {
            this.editCarrelloService = new EditCarrelloService();
        } catch (SQLException e) {
            throw new ServletException("Failed to initialize EditCarrelloService", e);
        }
    }

    @Override
    protected void doGet(HttpServletRequest request, HttpServletResponse response)
            throws ServletException, IOException {
        try {
            HttpSession session = request.getSession();
            Carrello carrello = (Carrello) session.getAttribute("carrello");
            if (carrello == null) {
                response.sendError(HttpServletResponse.SC_BAD_REQUEST, "Carrello vuoto o non trovato.");
                return;
            }

            try {
                int idProdotto = Integer.parseInt(request.getParameter("prodotto"));
                String tipo = request.getParameter("tipo");
                int quantita = tipo.equals("cambiaquantita") ? Integer.parseInt(request.getParameter("quantita")) : 0;

                // Chiamata al service
                if (tipo.equals("cambiaquantita")) {
                    carrello = editCarrelloService.modificaQuantitaProdotto(carrello, idProdotto, quantita);
                } else if (tipo.equals("elimina")) {
                    carrello = editCarrelloService.eliminaProdotto(carrello, idProdotto);
                }

                // Aggiorna il carrello in sessione
                session.setAttribute("carrello", carrello);

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