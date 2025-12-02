package controller;

import model.beans.Prodotto;
import services.LandingPageService;

import javax.servlet.RequestDispatcher;
import javax.servlet.ServletException;
import javax.servlet.annotation.WebServlet;
import javax.servlet.http.HttpServlet;
import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;
import java.io.IOException;
import java.sql.SQLException;
import java.util.ArrayList;

@WebServlet(name = "landingpage", value = "/landingpage", loadOnStartup = 1)
public class landingpage extends HttpServlet {
    private LandingPageService landingPageService;

    @Override
    public void init() throws ServletException {
        try {
            this.landingPageService = new LandingPageService();
        } catch (SQLException e) {
            throw new ServletException("Failed to initialize LandingPageService", e);
        }
    }

    @Override
    protected void doGet(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
        try {
            ArrayList<Prodotto> prodotti = landingPageService.getUltimiProdotti();
            request.setAttribute("prodotti", prodotti);

        } catch (SQLException e) {
            e.printStackTrace();
            response.sendError(HttpServletResponse.SC_INTERNAL_SERVER_ERROR);
            return;
        }

        String address = "/index.jsp";
        RequestDispatcher dispatcher = request.getRequestDispatcher(address);
        dispatcher.forward(request, response);
    }

    @Override
    protected void doPost(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
        doGet(request, response);
    }
}

