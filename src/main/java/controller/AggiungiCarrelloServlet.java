package controller;

import model.beans.Carrello;
import services.AggiungiCarrelloService;

import java.sql.SQLException;


import javax.servlet.ServletException;
import javax.servlet.annotation.WebServlet;
import javax.servlet.http.HttpServlet;
import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;
import javax.servlet.http.HttpSession;
import java.io.IOException;

@WebServlet(name = "AggiungiCarrelloServlet", value = "/AggiungiCarrelloServlet")
public class AggiungiCarrelloServlet extends HttpServlet {

    private AggiungiCarrelloService carrelloService;

    @Override
    public void init() throws ServletException {
        try {
            this.carrelloService = new AggiungiCarrelloService();
        } catch (SQLException e) {
            throw new ServletException("Failed to initialize AggiungiCarrelloService", e);
        }
    }


    @Override
    protected void doGet(HttpServletRequest request, HttpServletResponse response)
            throws ServletException, IOException {

        HttpSession session = request.getSession();

        try {
            int idProdotto = Integer.parseInt(request.getParameter("prodotto"));
            int quantita = Integer.parseInt(request.getParameter("quantita"));
            Carrello carrello = (Carrello) session.getAttribute("carrello");
            Carrello carrelloAggiornato =
                    carrelloService.aggiungiAlCarrello(carrello, idProdotto, quantita);

            session.setAttribute("carrello", carrelloAggiornato);

            request.getRequestDispatcher("/carrello.jsp").forward(request, response);

        } catch (Exception e) {
            e.printStackTrace();
            response.sendError(HttpServletResponse.SC_INTERNAL_SERVER_ERROR);
        }
    }

    @Override
    protected void doPost(HttpServletRequest request, HttpServletResponse response)
            throws ServletException, IOException {
        doGet(request, response);
    }
}
