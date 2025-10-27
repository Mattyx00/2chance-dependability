package controller;

import model.beans.Prodotto;
import model.dao.ProdottoDAO;

import javax.servlet.*;
import javax.servlet.http.*;
import javax.servlet.annotation.*;
import java.io.IOException;
import java.sql.SQLException;
import java.util.ArrayList;

@WebServlet(name = "ProdottiPerCategoriaServlet", value = "/ProdottiPerCategoriaServlet")
public class ProdottiPerCategoriaServlet extends HttpServlet {
    @Override
    protected void doGet(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
        try {
            ProdottoDAO dao = new ProdottoDAO();
            ArrayList<Prodotto> prodotti = dao.getProdottiByCategoria(request.getParameter("val"));
            request.setAttribute("prodotti", prodotti);
            String address = "/showProdotti.jsp";
            RequestDispatcher dispatcher = request.getRequestDispatcher(address);
            dispatcher.forward(request, response);

        } catch (SQLException e) {
            e.printStackTrace();
        }

    }

    @Override
    protected void doPost(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
        doGet(request, response);
    }
}
