package controller;

import model.beans.Prodotto;
import services.RicercaService;

import utils.ResponseUtils;

import javax.servlet.RequestDispatcher;
import javax.servlet.ServletException;
import javax.servlet.annotation.WebServlet;
import javax.servlet.http.HttpServlet;
import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;
import java.io.IOException;
import java.sql.SQLException;
import java.util.ArrayList;

@WebServlet(name = "RicercaServlet", value = "/RicercaServlet")
public class RicercaServlet extends HttpServlet {
    private RicercaService ricercaService;

    @Override
    public void init() throws ServletException {
        try {
            this.ricercaService = new RicercaService();
        } catch (SQLException e) {
            throw new ServletException("Failed to initialize RicercaService", e);
        }
    }

    @Override
    protected void doGet(HttpServletRequest request, HttpServletResponse response)
            throws ServletException, IOException {
        try {
            try {
                ArrayList<Prodotto> prodotti = ricercaService.cercaProdotti("%" + request.getParameter("val") + "%");
                request.setAttribute("prodotti", prodotti);
                String address = "/showProdotti.jsp";
                RequestDispatcher dispatcher = request.getRequestDispatcher(address);
                dispatcher.forward(request, response);
            } catch (SQLException e) {
                e.printStackTrace();
                response.sendError(HttpServletResponse.SC_INTERNAL_SERVER_ERROR);
            }
        } catch (Exception e) {
            e.printStackTrace();
            ResponseUtils.sendError(response, HttpServletResponse.SC_INTERNAL_SERVER_ERROR);
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
