package controller;

import model.beans.Prodotto;
import services.ProdottoService;

import javax.servlet.RequestDispatcher;
import javax.servlet.ServletException;
import javax.servlet.annotation.WebServlet;
import javax.servlet.http.HttpServlet;
import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;
import java.io.IOException;
import java.sql.SQLException;

@WebServlet(name = "ProdottoServlet", value = "/ProdottoServlet")
public class ProdottoServlet extends HttpServlet {
    private ProdottoService prodottoService;

    @Override
    public void init() throws ServletException {
        try {
            this.prodottoService = new ProdottoService();
        } catch (SQLException e) {
            throw new ServletException("Failed to initialize ProdottoService", e);
        }
    }

    @Override
    protected void doGet(HttpServletRequest request, HttpServletResponse response)
            throws ServletException, IOException {
        try {
            try {
                Prodotto prod = prodottoService.getProdottoById(Integer.parseInt(request.getParameter("prodotto")));
                request.setAttribute("prodotto", prod);

                String address = "/paginaProdotto.jsp";
                RequestDispatcher dispatcher = request.getRequestDispatcher(address);
                dispatcher.forward(request, response);

            } catch (SQLException throwables) {
                throwables.printStackTrace();
                response.sendError(HttpServletResponse.SC_INTERNAL_SERVER_ERROR);
            }
        } catch (Exception e) {
            e.printStackTrace();
            if (!response.isCommitted()) {
                response.sendError(HttpServletResponse.SC_INTERNAL_SERVER_ERROR);
            }
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
