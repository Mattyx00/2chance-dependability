package controller;

import model.beans.Prodotto;
import services.ConfrontaService;

import java.sql.SQLException;

import javax.servlet.ServletException;
import javax.servlet.annotation.WebServlet;
import javax.servlet.http.HttpServlet;
import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;
import java.io.IOException;

@WebServlet(name = "ConfrontaServlet", value = "/ConfrontaServlet")
public class ConfrontaServlet extends HttpServlet {

    private ConfrontaService confrontaService;

    @Override
    public void init() throws ServletException {
        try {
            this.confrontaService = new ConfrontaService();
        } catch (SQLException e) {
            throw new ServletException("Failed to initialize ConfrontaService", e);
        }
    }

    @Override
    protected void doGet(HttpServletRequest request, HttpServletResponse response)
            throws ServletException, IOException {

        try {
            try {
                int id1 = Integer.parseInt(request.getParameter("prodotto1"));
                int id2 = Integer.parseInt(request.getParameter("prodotto2"));

                Prodotto[] prodotti = confrontaService.confrontaProdotti(id1, id2);

                request.setAttribute("confronto1", prodotti[0]);
                request.setAttribute("confronto2", prodotti[1]);

                request.getRequestDispatcher("/confronta.jsp").forward(request, response);

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
