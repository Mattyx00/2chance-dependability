package controller;

import model.beans.Prodotto;
import services.ProdottiPerCategoriaService;

import javax.servlet.RequestDispatcher;
import javax.servlet.ServletException;
import javax.servlet.annotation.WebServlet;
import javax.servlet.http.HttpServlet;
import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;
import java.io.IOException;
import java.sql.SQLException;
import java.util.ArrayList;

@WebServlet(name = "ProdottiPerCategoriaServlet", value = "/ProdottiPerCategoriaServlet")
public class ProdottiPerCategoriaServlet extends HttpServlet {
    private ProdottiPerCategoriaService prodottiPerCategoriaService;

    @Override
    public void init() throws ServletException {
        try {
            this.prodottiPerCategoriaService = new ProdottiPerCategoriaService();
        } catch (SQLException e) {
            throw new ServletException("Failed to initialize ProdottiPerCategoriaService", e);
        }
    }

    @Override
    protected void doGet(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
        try {
            ArrayList<Prodotto> prodotti = prodottiPerCategoriaService.getProdottiByCategoria(request.getParameter("val"));
            request.setAttribute("prodotti", prodotti);
            String address = "/showProdotti.jsp";
            RequestDispatcher dispatcher = request.getRequestDispatcher(address);
            dispatcher.forward(request, response);

        } catch (SQLException e) {
            e.printStackTrace();
            response.sendError(HttpServletResponse.SC_INTERNAL_SERVER_ERROR);
        }
    }

    @Override
    protected void doPost(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
        doGet(request, response);
    }
}

